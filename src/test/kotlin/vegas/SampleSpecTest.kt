package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldContainExactlyInAnyOrder
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.frontend.parseFile
import vegas.ir.Dist
import vegas.ir.EntropySource
import vegas.ir.Expr

/**
 * Per-node SampleSpec wiring and surface dist syntax.
 *
 * Every action owned by a chance role gets a SampleSpec; the prior is
 * either an explicit `~ uniform/weighted { ... }` annotation lowered from
 * the surface, or — failing that — an inferred uniform over the parameter
 * domain. Multi-parameter / unbounded-int chance actions land with
 * dist=null and backends fall back to uniform-over-surviving-moves.
 */
class SampleSpecTest : FreeSpec({

    "Dist invariants" - {

        "uniform builds a normalized distribution" {
            val d = Dist.uniform(listOf(
                Expr.Const.IntVal(0),
                Expr.Const.IntVal(1),
                Expr.Const.IntVal(2),
            ))
            d.support.size shouldBe 3
            d.weight(Expr.Const.IntVal(1)) shouldBe Rational(1, 3)
            d.weight(Expr.Const.IntVal(9)) shouldBe null
        }

        "rejects empty support" {
            shouldThrow<IllegalArgumentException> {
                Dist.uniform(emptyList())
            }
        }

        "rejects duplicate keys" {
            shouldThrow<IllegalArgumentException> {
                Dist(listOf(
                    Expr.Const.IntVal(0) to Rational(1, 2),
                    Expr.Const.IntVal(0) to Rational(1, 2),
                ))
            }
        }

        "rejects weights that do not sum to 1" {
            shouldThrow<IllegalArgumentException> {
                Dist(listOf(
                    Expr.Const.IntVal(0) to Rational(1, 3),
                    Expr.Const.IntVal(1) to Rational(1, 3),
                ))
            }
        }

        "rejects non-positive weights" {
            shouldThrow<IllegalArgumentException> {
                Dist(listOf(
                    Expr.Const.IntVal(0) to Rational(0),
                    Expr.Const.IntVal(1) to Rational(1),
                ))
            }
        }
    }

    "SampleSpec wiring from chance roles" - {

        "MontyHallChance: Host's draw nodes are sample nodes with uniform dist over the door domain" {
            val ast = parseFile("examples/MontyHallChance.vg")
            val ir = compileToIR(ast)
            val host = RoleId("Host")

            host shouldBe (ir.chanceRoles.singleOrNull() ?: error("Host should be the only chance role"))

            // The car-bearing actions (commit + reveal) are owned by Host
            // and write a door parameter. They should be sample nodes with
            // a uniform-over-{0,1,2} prior.
            val carNodes = ir.dag.actions
                .filter { ir.dag.owner(it) == host }
                .filter { node ->
                    ir.dag.writes(node).any { it.param == VarId("car") }
                }

            carNodes.shouldNotBeNull()
            check(carNodes.isNotEmpty()) { "expected at least one Host node writing car" }

            for (n in carNodes) {
                val spec = ir.dag.sampleSpec(n)
                spec.shouldNotBeNull()
                spec.source shouldBe EntropySource.RoleSubmit(host)
                val dist = spec.dist
                dist.shouldNotBeNull()
                dist.values shouldContainExactlyInAnyOrder listOf(
                    Expr.Const.IntVal(0),
                    Expr.Const.IntVal(1),
                    Expr.Const.IntVal(2),
                )
                // uniform
                for (v in dist.values) {
                    dist.weight(v) shouldBe Rational(1, 3)
                }
            }
        }

        "Strategic roles get no sample spec" {
            val ast = parseFile("examples/MontyHallChance.vg")
            val ir = compileToIR(ast)
            val guest = RoleId("Guest")

            val guestNodes = ir.dag.actions.filter { ir.dag.owner(it) == guest }
            for (n in guestNodes) {
                ir.dag.sampleSpec(n) shouldBe null
                ir.dag.isSampleNode(n) shouldBe false
            }
        }

        "Join steps of chance roles are not sample nodes" {
            // A chance role's join step has no parameters and is not itself a
            // random draw; only its later yield/commit/reveal nodes are.
            val ast = parseFile("examples/MontyHallChance.vg")
            val ir = compileToIR(ast)
            val host = RoleId("Host")

            val hostJoin = ir.dag.actions
                .filter { ir.dag.owner(it) == host }
                .single { ir.dag.spec(it).join != null }

            ir.dag.sampleSpec(hostJoin) shouldBe null
            ir.dag.isSampleNode(hostJoin) shouldBe false
        }
    }

    "Surface `~ uniform/weighted` annotation" - {

        "uniform overrides the inferred prior with the same values" {
            val src = """
                type door = {0, 1, 2}
                game main() {
                  random Host() ${'$'} 100;
                  join Guest() ${'$'} 100;
                  yield Host(car: door ~ uniform { 0, 1, 2 });
                  yield Guest(d: door);
                  withdraw { Host -> Guest.d == Host.car ? 0 : 200; Guest -> Guest.d == Host.car ? 200 : 0; }
                }
            """.trimIndent()
            val ir = compileToIR(parseCode(src))
            val host = RoleId("Host")
            val carNode = ir.dag.actions.single { ir.dag.owner(it) == host && ir.dag.spec(it).join == null }
            val dist = ir.dag.sampleSpec(carNode)?.dist
            dist.shouldNotBeNull()
            for (v in dist.values) dist.weight(v) shouldBe Rational(1, 3)
        }

        "weighted produces a non-uniform prior that Gambit emits" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin() ${'$'} 10;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 });
                  yield Bettor(call: face);
                  withdraw { Coin -> 0; Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = compileToIR(parseCode(src))
            val coin = RoleId("Coin")
            val sampleNode = ir.dag.actions.single { ir.dag.owner(it) == coin && ir.dag.spec(it).join == null }
            val dist = ir.dag.sampleSpec(sampleNode)?.dist
            dist.shouldNotBeNull()
            dist.weight(Expr.Const.IntVal(0)) shouldBe Rational(3, 4)
            dist.weight(Expr.Const.IntVal(1)) shouldBe Rational(1, 4)

            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)
            efg shouldContain "3/4"
            efg shouldContain "1/4"
        }

        "rejects ~ on strategic role" {
            val src = """
                type face = {0, 1}
                game main() {
                  join A() ${'$'} 10 B() ${'$'} 10;
                  yield A(x: face ~ uniform { 0, 1 });
                  yield B(y: face);
                  withdraw { A -> A.x == B.y ? 20 : 0; B -> A.x == B.y ? 0 : 20; }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "rejects values outside the parameter type" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin() ${'$'} 10;
                  join B() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1, 7 });
                  yield B(call: face);
                  withdraw { Coin -> 0; B -> B.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }
    }

    "Codex findings" - {

        "weighted dist survives automatic commit-reveal expansion" {
            // A pure-public sample that is concurrent with a strategic
            // pure-public action gets split into commit+reveal nodes by
            // EventGraph.expandCommitReveal; the commit-node delta stores
            // Hidden(v). Gambit's prior lookup must unwrap Hidden so the
            // declared weights survive the rewrite.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin() ${'$'} 10;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 }) Bettor(call: face);
                  withdraw { Coin -> 0; Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = compileToIR(parseCode(src))
            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)
            efg shouldContain "3/4"
            efg shouldContain "1/4"
        }

        "rejects two parameters both carrying ~ annotations" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Pair() ${'$'} 10;
                  join B() ${'$'} 10;
                  yield Pair(a: face ~ uniform { 0, 1 }, b: face ~ uniform { 0, 1 });
                  yield B(call: face);
                  withdraw { Pair -> 0; B -> B.call == Pair.a ? 20 : 0 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "Dist rejects Rational with negative denominator that looks positive" {
            // Rational does not normalize sign at construction; a naïve
            // `numerator > 0` check would accept this negative weight.
            shouldThrow<IllegalArgumentException> {
                Dist(listOf(
                    Expr.Const.IntVal(0) to Rational(1, -2),
                    Expr.Const.IntVal(1) to Rational(3, 2),
                ))
            }
        }

        "MAID emits a chance CPD reflecting the declared weights" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin() ${'$'} 10;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 });
                  yield Bettor(call: face);
                  withdraw { Coin -> 0; Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = compileToIR(parseCode(src))
            val maid = vegas.backend.maid.generateMaid(ir)
            val coinNode = maid.nodes.single { it.type == vegas.backend.maid.MaidNodeType.CHANCE }
            val cpd = maid.cpds.single { it.node == coinNode.id }
            // Domain ordering is the typeToDomain order: [0, 1] for the
            // {0, 1} range. The CPD has one column (no parents).
            cpd.values.size shouldBe 2
            cpd.values[0].single() shouldBe 0.75
            cpd.values[1].single() shouldBe 0.25
        }

        "rejects ~ on a single parameter of a multi-parameter action" {
            // A single ~ on one of several parameters would silently lose
            // the annotation at lowering (singleOrNull is null when there
            // are 2+ params). Reject at the typechecker instead.
            val src = """
                type face = {0, 1}
                game main() {
                  random Pair() ${'$'} 10;
                  join B() ${'$'} 10;
                  yield Pair(a: face ~ weighted { 0: 3, 1: 1 }, b: face);
                  yield B(call: face);
                  withdraw { Pair -> 0; B -> B.call == Pair.a ? 20 : 0 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "MAID chance CPD folds self-only guard into the prior" {
            // The guard `where Coin.side != 1` is self-only (reads only the
            // sampled field) so it should restrict the prior to {0} and
            // renormalize to a deterministic distribution.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin() ${'$'} 10;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where Coin.side != 1;
                  yield Bettor(call: face);
                  withdraw { Coin -> 0; Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = compileToIR(parseCode(src))
            val maid = vegas.backend.maid.generateMaid(ir)
            val coinNode = maid.nodes.single { it.type == vegas.backend.maid.MaidNodeType.CHANCE }
            val cpd = maid.cpds.single { it.node == coinNode.id }
            cpd.values.size shouldBe 2
            cpd.values[0].single() shouldBe 1.0
            cpd.values[1].single() shouldBe 0.0
        }
    }
})

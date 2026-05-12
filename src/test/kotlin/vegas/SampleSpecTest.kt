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
 * the surface, or (failing that) an inferred uniform over the parameter
 * domain. Multi-parameter / unbounded-int chance actions land with
 * dist=null and backends fall back to uniform-over-surviving-moves.
 */
/**
 * Parse, typecheck, and lower a source string in one call. Tests that
 * assert specific IR / backend output for a *valid* program should use
 * this helper rather than going directly through compileToIR: typecheck
 * gates the program against the same rules production code applies, so
 * sources that violate (e.g.) the random-in-withdraw prohibition don't
 * silently get past the harness.
 */
private fun typedCompile(src: String) = run {
    val ast = vegas.frontend.parseCode(src)
    vegas.typeCheck(ast)
    vegas.frontend.compileToIR(ast)
}

/** typecheck-then-compile from an example file path. */
private fun typedCompileFile(path: String) = run {
    val ast = vegas.frontend.parseFile(path)
    vegas.typeCheck(ast)
    vegas.frontend.compileToIR(ast)
}

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
            val ir = typedCompileFile("examples/MontyHallChance.vg")
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
            val ir = typedCompileFile("examples/MontyHallChance.vg")
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
            val ir = typedCompileFile("examples/MontyHallChance.vg")
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
                  random Host;
                  join Guest() ${'$'} 100;
                  yield Host(car: door ~ uniform { 0, 1, 2 });
                  yield Guest(d: door);
                  withdraw (Guest.d == Host.car) ? { Guest -> 100 } : { Guest -> 0; burn 100 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
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
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 });
                  yield Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
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
                  random Coin;
                  join B() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1, 7 });
                  yield B(call: face);
                  withdraw { B -> B.call == Coin.side ? 20 : 0 }
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
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 }) Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)
            efg shouldContain "3/4"
            efg shouldContain "1/4"
        }

        "rejects two parameters both carrying ~ annotations" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Pair;
                  join B() ${'$'} 10;
                  yield Pair(a: face ~ uniform { 0, 1 }, b: face ~ uniform { 0, 1 });
                  yield B(call: face);
                  withdraw { B -> B.call == Pair.a ? 20 : 0 }
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
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 });
                  yield Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
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
                  random Pair;
                  join B() ${'$'} 10;
                  yield Pair(a: face ~ weighted { 0: 3, 1: 1 }, b: face);
                  yield B(call: face);
                  withdraw { B -> B.call == Pair.a ? 20 : 0 }
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
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where Coin.side != 1;
                  yield Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val maid = vegas.backend.maid.generateMaid(ir)
            val coinNode = maid.nodes.single { it.type == vegas.backend.maid.MaidNodeType.CHANCE }
            val cpd = maid.cpds.single { it.node == coinNode.id }
            cpd.values.size shouldBe 2
            cpd.values[0].single() shouldBe 1.0
            cpd.values[1].single() shouldBe 0.0
        }

        "MAID chance CPD folds self-only guard even after commit-reveal expansion" {
            // The Coin sample is pure-public and concurrent with Bettor's
            // yield, so EventGraph.expandCommitReveal splits Coin into
            // commit (guard = true) + reveal (original guard). The chance
            // CPD must use the reveal node's guard, not the commit's, or
            // it would emit the unprojected prior 0.5/0.5.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where Coin.side != 1
                        Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val maid = vegas.backend.maid.generateMaid(ir)
            val coinNode = maid.nodes.single {
                it.type == vegas.backend.maid.MaidNodeType.CHANCE
            }
            val cpd = maid.cpds.single { it.node == coinNode.id }
            cpd.values.size shouldBe 2
            cpd.values[0].single() shouldBe 1.0
            cpd.values[1].single() shouldBe 0.0
        }

        "Gambit emits a deterministic chance branch when commit-reveal expansion meets a self-only guard" {
            // Same shape as the MAID test: Coin's pure-public sample is
            // concurrent with Bettor, so expandCommitReveal splits it.
            // With the self-only guard moved onto the commit, Gambit sees
            // a single guarded chance decision and emits only the legal
            // branch (side = 0). Bettor's own commit is still binary
            // (Bettor picks 0 or 1 for `call`), so we check chance nodes
            // specifically.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where Coin.side != 1
                        Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)
            val chanceLines = efg.lines().filter { it.startsWith("c ") }
            check(chanceLines.isNotEmpty()) { "no chance lines in EFG:\n$efg" }
            for (line in chanceLines) {
                check(!line.contains("Hidden(1)")) {
                    "chance node enumerates Hidden(1); guard projection on commit-expanded sample failed: $line"
                }
            }
            // At least one chance node should be the Coin commit, picking only Hidden(0).
            check(chanceLines.any { it.contains("\"Hidden(0)\" 1") }) {
                "expected a deterministic chance branch on Hidden(0); got:\n${chanceLines.joinToString("\n")}"
            }
        }

        "Gambit honors partial-support priors instead of falling back to uniform" {
            // The dist's declared support is {0, 1} but the type domain is
            // {0, 1, 2}. Enumerating the full type would generate a phantom
            // 2-branch with no prior weight, tripping the all-declared
            // check and emitting uniform 1/3 instead of 3/4 / 1/4.
            val src = """
                type face = {0 .. 2}
                game main() {
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ weighted { 0: 3, 1: 1 });
                  yield Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)
            val chanceLines = efg.lines().filter { it.startsWith("c ") }
            check(chanceLines.isNotEmpty()) { "no chance lines in EFG:\n$efg" }
            // The chance node must enumerate only {0, 1}, not 2.
            for (line in chanceLines) {
                check(!Regex("""\b"?2"?\b""").containsMatchIn(line.substringAfter("{").substringBefore("}"))) {
                    "chance enumerated value 2 outside dist support: $line"
                }
            }
            efg shouldContain "3/4"
            efg shouldContain "1/4"
            check(!efg.contains("1/3")) {
                "uniform 1/3 fallback was emitted despite explicit weighted prior:\n$efg"
            }
        }

        "MAID emits a uniform CPD when a chance node has no explicit Dist" {
            // A multi-parameter chance action produces dist = null at IR
            // lowering (joint distributions are not yet supported), but the
            // MAID nodes must still carry a probability table, or the
            // resulting MAID is malformed. Fall back to uniform-over-domain.
            val src = """
                type face = {0, 1}
                game main() {
                  random Pair;
                  join B() ${'$'} 10;
                  yield Pair(a: face, b: face);
                  yield B(call: face);
                  withdraw { B -> B.call == Pair.a ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val maid = vegas.backend.maid.generateMaid(ir)
            val chanceNodes = maid.nodes.filter { it.type == vegas.backend.maid.MaidNodeType.CHANCE }
            check(chanceNodes.size == 2) { "expected 2 chance nodes (a, b); got $chanceNodes" }
            for (n in chanceNodes) {
                val cpd = maid.cpds.single { it.node == n.id }
                cpd.values.size shouldBe 2
                for (row in cpd.values) {
                    for (p in row) p shouldBe 0.5
                }
            }
        }

        "Gambit rejects a chance node whose self-only guard is unsatisfiable" {
            // `where false` is a self-only guard that kills every value in
            // the prior support. The compiler must surface this as a static
            // error from the Gambit pipeline, not silently emit a broken
            // chance node or crash with the internal FinalizeFrontier check.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where false
                        Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            shouldThrow<StaticError> {
                generateExtensiveFormGame(ir, includeAbandonment = false)
            }
        }

        "MAID rejects a chance node whose self-only guard is unsatisfiable" {
            // Empty support after projection means the sample cannot fire;
            // emitting any CPD silently would be wrong. Throw instead.
            val src = """
                type face = {0, 1}
                game main() {
                  random Coin;
                  join Bettor() ${'$'} 10;
                  yield Coin(side: face ~ uniform { 0, 1 }) where Coin.side != 0 && Coin.side != 1;
                  yield Bettor(call: face);
                  withdraw { Bettor -> Bettor.call == Coin.side ? 20 : 0 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            shouldThrow<IllegalStateException> { vegas.backend.maid.generateMaid(ir) }
        }
    }

    "Burn lowering" - {

        "burn N reaches the IR as GameIR.burn" {
            val src = """
                type face = {0, 1}
                game main() {
                  join P() ${'$'} 10;
                  sample (w: face);
                  yield P(g: face);
                  withdraw (P.g == Sample.w) ? { P -> 10 } : { P -> 0; burn 10 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            // burn must be a non-trivial expression (an Ite over the
            // outcome condition) rather than the default constant 0.
            check(ir.burn !is Expr.Const.IntVal || (ir.burn as Expr.Const.IntVal).v != 0) {
                "Expected ir.burn to encode the conditional burn expression; got ${ir.burn}"
            }
        }

        "burn N in a non-conditional outcome lowers to a constant" {
            val src = """
                game main() {
                  join P() ${'$'} 10;
                  yield P(g: bool);
                  withdraw { P -> 0; burn 10 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            ir.burn shouldBe Expr.Const.IntVal(10)
        }

        "let-bound variable inside a burn expression substitutes correctly" {
            // The let-substitution in Transform.kt used to drop the burn
            // field when reconstructing Outcome.Value. With burn referring
            // to a let-bound variable, the IR would have either lost the
            // burn entirely or referenced an unbound name.
            val src = """
                game main() {
                  join P() ${'$'} 10;
                  yield P(g: bool);
                  withdraw let x: int = 7 in { P -> 0; burn x }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            ir.burn shouldBe Expr.Const.IntVal(7)
        }

        "no burn item leaves GameIR.burn at the default 0" {
            val src = """
                game main() {
                  join P() ${'$'} 10;
                  yield P(g: bool);
                  withdraw { P -> 10 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            ir.burn shouldBe Expr.Const.IntVal(0)
        }
    }

    "Anonymous public sample and burn" - {

        "sample binds a field under the synthetic Sample owner" {
            val src = """
                type face = {0, 1}
                game main() {
                  join P() ${'$'} 10;
                  sample (w: face);
                  yield P(guess: face);
                  withdraw (P.guess == Sample.w) ? { P -> 10 } : { P -> 0; burn 10 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val sampleOwner = vegas.frontend.SAMPLE_OWNER
            // The sample binding produces a sample node owned by the
            // synthetic owner with uniform-over-domain inferred.
            sampleOwner shouldBe ir.chanceRoles.single()
            val sampleNode = ir.dag.actions.single { ir.dag.owner(it) == sampleOwner }
            val spec = ir.dag.sampleSpec(sampleNode)
            spec.shouldNotBeNull()
            val dist = spec.dist
            dist.shouldNotBeNull()
            dist.values shouldContainExactlyInAnyOrder listOf(
                Expr.Const.IntVal(0),
                Expr.Const.IntVal(1),
            )
        }

        "sample with explicit ~ weighted" {
            val src = """
                type face = {0, 1}
                game main() {
                  join P() ${'$'} 10;
                  sample (w: face ~ weighted { 0: 3, 1: 1 });
                  yield P(guess: face);
                  withdraw (P.guess == Sample.w) ? { P -> 10 } : { P -> 0; burn 10 }
                }
            """.trimIndent()
            val ir = typedCompile(src)
            val sampleOwner = vegas.frontend.SAMPLE_OWNER
            val sampleNode = ir.dag.actions.single { ir.dag.owner(it) == sampleOwner }
            val dist = ir.dag.sampleSpec(sampleNode)?.dist
            dist.shouldNotBeNull()
            dist.weight(Expr.Const.IntVal(0)) shouldBe Rational(3, 4)
            dist.weight(Expr.Const.IntVal(1)) shouldBe Rational(1, 4)
        }

        "typechecker rejects a random role appearing in withdraw" {
            val src = """
                type face = {0, 1}
                game main() {
                  random Host;
                  join G() ${'$'} 10;
                  commit Host(c: face);
                  yield G(g: face);
                  reveal Host(c: face);
                  withdraw { G -> 10; Host -> 0 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "typechecker reserves the Sample owner name" {
            val src = """
                game main() {
                  join Sample() ${'$'} 10;
                  withdraw { Sample -> 10 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "typechecker rejects ~ D on a reveal step" {
            // The dist annotation must bind at the commit where the value
            // is drawn, not at the reveal. Allowing it on reveal would
            // attach a phantom SampleSpec to the reveal node and confuse
            // every backend (commit-reveal expansion already propagates
            // the originating commit's metadata).
            val src = """
                type face = {0, 1}
                game main() {
                  random Host;
                  join G() ${'$'} 10;
                  commit Host(c: face);
                  yield G(g: face);
                  reveal Host(c: face ~ uniform { 0, 1 });
                  withdraw { G -> 10 }
                }
            """.trimIndent()
            shouldThrow<StaticError> { typeCheck(parseCode(src)) }
        }

        "parser rejects deposits on random (no silent recovery)" {
            // `random Coin() $ 10;` used to be silently accepted via ANTLR
            // error recovery (the `$ 10` was skipped). The strict parser
            // now reports the extraneous input as a hard error.
            val src = """
                game main() {
                  random Coin() ${'$'} 10;
                  join P() ${'$'} 10;
                  yield Coin(side: int);
                  yield P(call: int);
                  withdraw { P -> 10 }
                }
            """.trimIndent()
            shouldThrow<vegas.frontend.VegasParseError> { parseCode(src) }
        }

        "Solidity emits no role gate, no actor slots, no withdraw for sample" {
            // Sample bindings have no actor and no payout, so the generated
            // Solidity must not include:
            //   * by(Role.Sample) modifier (would be uncallable)
            //   * address_Sample / done_Sample / claimed_Sample slots
            //   * withdraw_Sample function
            // Strategic role gates are still expected.
            val ir = typedCompileFile("examples/Lottery.vg")
            val contract = vegas.backend.evm.compileToEvm(ir)
            val sol = vegas.backend.evm.generateSolidity(contract)
            for (forbidden in listOf(
                "by(Role.Sample)",
                "address_Sample",
                "done_Sample ",
                "done_Sample;",
                "claimed_Sample",
                "withdraw_Sample",
            )) {
                check(!sol.contains(forbidden)) { "Solidity contains '$forbidden':\n$sol" }
            }
            check(sol.contains("by(Role.P1)")) {
                "Expected by(Role.P1) on strategic actions; got Solidity without it"
            }
            // The sampled field storage (Sample_w) is still required.
            check(sol.contains("Sample_w")) {
                "Expected sampled field Sample_w to be stored"
            }
        }
    }
})

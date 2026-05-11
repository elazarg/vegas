package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldContainExactlyInAnyOrder
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.ir.Dist
import vegas.ir.EntropySource
import vegas.ir.Expr

/**
 * Per-node SampleSpec wiring (Stage 1 of probabilistic-design).
 *
 * Pins down the additive refactor that moves chance from a per-role flag to
 * a per-node metadata carrier: every action owned by a chance role gets a
 * SampleSpec with a uniform prior over its parameter domain and a
 * RoleSubmit source. Multi-parameter / unbounded-int chance actions still
 * land with dist=null and backends fall back to legacy behavior.
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
})

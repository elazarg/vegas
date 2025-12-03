package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import vegas.semantics.Configuration
import vegas.semantics.History
import vegas.semantics.reconstructViews
import vegas.semantics.redacted
import vegas.dag.FrontierMachine
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.ir.Expr

/**
 * Test suite for Configuration data class.
 *
 * Tests the new Configuration abstraction that represents a configuration Γ
 * in the LTS.
 */
class ConfigurationTest : FreeSpec({

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")

    fun compileGame(code: String) = compileToIR(parseCode(code))

    "Configuration data class" - {

        "delegates isTerminal to frontier" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val frontier = FrontierMachine.from(ir.dag)
            val config = Configuration(frontier, History())

            // Should delegate to frontier.isComplete()
            config.isTerminal() shouldBe frontier.isComplete()
        }

        "delegates enabled to frontier" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val frontier = FrontierMachine.from(ir.dag)
            val config = Configuration(frontier, History())

            config.enabled() shouldBe frontier.enabled()
        }

        "actionsByRole groups by owner" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val frontier = FrontierMachine.from(ir.dag)
            val config = Configuration(frontier, History())

            val byRole = config.actionsByRole(ir.dag)
            // Should have Alice's actions grouped
            byRole[alice]?.isNotEmpty() shouldBe true
        }

        "rolesWithParams filters correctly" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val frontier = FrontierMachine.from(ir.dag)
            val config = Configuration(frontier, History())

            val rolesWithParams = config.rolesWithParams(ir.dag)
            // At initial frontier, join has no parameters, so set should be empty
            rolesWithParams shouldBe emptySet()
        }
    }

    "hasActed detection" - {

        "returns false when partial is empty" {
            val ir = compileGame("join Alice() $ 100; withdraw { Alice -> 10 }")
            val frontier = FrontierMachine.from(ir.dag)
            val config = Configuration(frontier, History(), emptyMap())

            config.hasActed(alice) shouldBe false
        }

        "returns true when role has field in partial" {
            val ir = compileGame("join Alice() $ 100; withdraw { Alice -> 10 }")
            val frontier = FrontierMachine.from(ir.dag)
            val partial = mapOf(FieldRef(alice, VarId("x")) to Expr.Const.BoolVal(true))
            val config = Configuration(frontier, History(), partial)

            config.hasActed(alice) shouldBe true
        }

        "returns false for other roles" {
            val ir = compileGame("join Alice() $ 100; withdraw { Alice -> 10 }")
            val frontier = FrontierMachine.from(ir.dag)
            val partial = mapOf(FieldRef(alice, VarId("x")) to Expr.Const.BoolVal(true))
            val config = Configuration(frontier, History(), partial)

            config.hasActed(bob) shouldBe false
        }

        "detects any field from the role" {
            val ir = compileGame("join Alice() $ 100; withdraw { Alice -> 10 }")
            val frontier = FrontierMachine.from(ir.dag)
            val partial = mapOf(
                FieldRef(alice, VarId("x")) to Expr.Const.BoolVal(true),
                FieldRef(alice, VarId("y")) to Expr.Const.IntVal(42)
            )
            val config = Configuration(frontier, History(), partial)

            config.hasActed(alice) shouldBe true
        }

        "works with Quit values" {
            val ir = compileGame("join Alice() $ 100; withdraw { Alice -> 10 }")
            val frontier = FrontierMachine.from(ir.dag)
            val partial = mapOf(FieldRef(alice, VarId("x")) to Expr.Const.Quit)
            val config = Configuration(frontier, History(), partial)

            config.hasActed(alice) shouldBe true
        }
    }

    "views function" - {

        "uses redacted from GameState" {
            val aliceField = FieldRef(alice, VarId("x"))
            val bobField = FieldRef(bob, VarId("y"))
            val slice = mapOf(
                aliceField to Expr.Const.Hidden(Expr.Const.BoolVal(true)),
                bobField to Expr.Const.IntVal(42)
            )

            // Direct redaction
            val aliceRedacted = redacted(slice, alice)
            val bobRedacted = redacted(slice, bob)

            // Alice sees unwrapped, Bob sees as-is
            aliceRedacted[aliceField] shouldBe Expr.Const.BoolVal(true)
            aliceRedacted[bobField] shouldBe Expr.Const.IntVal(42)

            // Bob sees Alice's as Opaque
            bobRedacted[aliceField] shouldBe Expr.Const.Opaque
            bobRedacted[bobField] shouldBe Expr.Const.IntVal(42)
        }

        "works with empty history" {
            val views = reconstructViews(History(), setOf(alice, bob))
            views.keys shouldBe setOf(alice, bob)
        }
    }
})
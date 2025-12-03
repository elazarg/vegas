package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.shouldBe
import vegas.backend.gambit.Configuration
import vegas.backend.gambit.GameSemantics
import vegas.backend.gambit.History
import vegas.backend.gambit.IrVal
import vegas.backend.gambit.Label
import vegas.backend.gambit.PlayTag
import vegas.dag.FrontierMachine
import vegas.frontend.compileToIR
import vegas.frontend.parseCode

/**
 * Test suite for GameSemantics.
 *
 * Tests the LTS move enumeration logic.
 */
class SemanticsTest : FreeSpec({

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")

    fun compileGame(code: String) = compileToIR(parseCode(code))

    "enabledMoves" - {

        "returns empty list at terminal" {
            val code = """
                join Alice() $ 100;
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance through all frontiers to terminal
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            while (!config.isTerminal()) {
                val moves = semantics.enabledMoves(config)
                if (moves.isEmpty()) break

                val move = moves.first()
                config = when (move) {
                    is Label.Play -> Configuration(config.frontier, config.history, config.partialFrontierAssignment + move.delta)
                    is Label.FinalizeFrontier -> Configuration(
                        config.frontier.resolveEnabled(),
                        config.history with config.partialFrontierAssignment,
                        emptyMap()
                    )
                }
            }

            // At terminal, should have no moves
            semantics.enabledMoves(config).shouldBeEmpty()
        }

        "includes explicit moves for roles with params" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Start at initial config, advance past join (no params)
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Now at yield Alice(x: bool) - should have explicit moves
            val moves = semantics.enabledMoves(config)
            val playMoves = moves.filterIsInstance<Label.Play>()
            val explicitMoves = playMoves.filter { it.tag is PlayTag.Action }

            explicitMoves.shouldHaveSize(2) // true, false
            explicitMoves.all { it.role == alice } shouldBe true
        }

        "excludes moves for roles that already acted" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice acts
            val moves = semantics.enabledMoves(config)
            val firstMove = moves.filterIsInstance<Label.Play>().first()
            config = Configuration(config.frontier, config.history, config.partialFrontierAssignment + firstMove.delta)

            // Now Alice has acted - should have no more Play moves for Alice
            val newMoves = semantics.enabledMoves(config)
            val newPlayMoves = newMoves.filterIsInstance<Label.Play>()

            newPlayMoves.shouldBeEmpty()
        }

        "includes quit moves for strategic players" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            val moves = semantics.enabledMoves(config)

            // Should have explicit moves + quit
            val playMoves = moves.filterIsInstance<Label.Play>()
            val quitMoves = playMoves.filter { it.tag is PlayTag.Quit }

            quitMoves.shouldHaveSize(1)
            quitMoves.first().role shouldBe alice
        }

        "excludes quit for roles that already quit" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier and have Alice quit
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice quits by having Quit in history
            val aliceField = FieldRef(alice, VarId("x"))
            val quitSlice = mapOf(aliceField to IrVal.Quit)
            val history = config.history with quitSlice
            config = Configuration(config.frontier.resolveEnabled(), history, emptyMap())

            // At next frontier, Alice should have no moves (already quit)
            val moves = semantics.enabledMoves(config)
            val aliceMoves = moves.filterIsInstance<Label.Play>().filter { it.role == alice }

            aliceMoves.shouldBeEmpty()
        }

        "excludes quit for roles that already acted in frontier" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice acts with explicit move
            val moves = semantics.enabledMoves(config)
            val explicitMove = moves.filterIsInstance<Label.Play>().first { it.tag is PlayTag.Action }
            config = Configuration(config.frontier, config.history, config.partialFrontierAssignment + explicitMove.delta)

            // Alice should have no quit move (already acted)
            val newMoves = semantics.enabledMoves(config)
            val quitMoves = newMoves.filterIsInstance<Label.Play>().filter { it.tag is PlayTag.Quit }

            quitMoves.shouldBeEmpty()
        }

        "no moves for roles without parameters" {
            val code = """
                join Alice() $ 100;
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // At initial frontier, Alice's join has no params
            val config = Configuration(FrontierMachine.from(ir.dag), History())
            val moves = semantics.enabledMoves(config)

            // Should have only FinalizeFrontier, no Play moves
            val playMoves = moves.filterIsInstance<Label.Play>()
            playMoves.shouldBeEmpty()

            val finalizingMoves = moves.filterIsInstance<Label.FinalizeFrontier>()
            finalizingMoves.shouldHaveSize(1)
        }
    }

    "canFinalizeFrontier" - {

        "enabled when all required roles acted" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice acts
            val moves = semantics.enabledMoves(config)
            val firstMove = moves.filterIsInstance<Label.Play>().first()
            config = Configuration(config.frontier, config.history, config.partialFrontierAssignment + firstMove.delta)

            // Alice acted, FinalizeFrontier should be enabled
            semantics.canFinalizeFrontier(config) shouldBe true
        }

        "disabled when some roles haven't acted" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice hasn't acted yet
            semantics.canFinalizeFrontier(config) shouldBe false
        }

        "disabled at terminal" {
            val code = """
                join Alice() $ 100;
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to terminal
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            semantics.canFinalizeFrontier(config) shouldBe false
        }

        "enabled when quit roles are ignored" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice quits in history
            val aliceField = FieldRef(alice, VarId("x"))
            val quitSlice = mapOf(aliceField to IrVal.Quit)
            config = Configuration(config.frontier, config.history with quitSlice, emptyMap())

            // No roles need to act (Alice quit), so FinalizeFrontier enabled
            semantics.canFinalizeFrontier(config) shouldBe true
        }

        "enabled when no roles have params" {
            val code = """
                join Alice() $ 100;
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // At join frontier (no params)
            val config = Configuration(FrontierMachine.from(ir.dag), History())

            // No roles have params, so FinalizeFrontier enabled immediately
            semantics.canFinalizeFrontier(config) shouldBe true
        }
    }
})

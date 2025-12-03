package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import vegas.backend.gambit.Configuration
import vegas.backend.gambit.GameSemantics
import vegas.backend.gambit.History
import vegas.backend.gambit.IrVal
import vegas.backend.gambit.Label
import vegas.backend.gambit.PlayTag
import vegas.backend.gambit.applyMove
import vegas.backend.gambit.quit
import vegas.dag.FrontierMachine
import vegas.frontend.compileToIR
import vegas.frontend.parseCode

/**
 * Test suite for transition application.
 *
 * Tests the applyMove function that implements the LTS transition relation
 */
class TransitionTest : FreeSpec({

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")

    fun compileGame(code: String) = compileToIR(parseCode(code))

    "applyMove Play" - {

        "merges delta into partial" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Start at yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Get a Play move
            val moves = semantics.enabledMoves(config)
            val playMove = moves.filterIsInstance<Label.Play>().first { it.tag is PlayTag.Action }

            // Apply the move
            val nextConfig = applyMove(config, playMove)

            // Partial should contain the delta
            nextConfig.partial shouldBe playMove.delta
            // Frontier and history should be unchanged
            nextConfig.frontier shouldBe config.frontier
            nextConfig.history shouldBe config.history
        }

        "accumulates multiple moves in partial" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(x: bool);
                yield Bob(y: bool);
                withdraw { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            // Advance to first yield frontier
            var config = Configuration(FrontierMachine.from(ir.dag), History())
            repeat(2) {
                config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())
            }

            // Alice acts
            val moves1 = semantics.enabledMoves(config)
            val aliceMove = moves1.filterIsInstance<Label.Play>().first { it.role == alice && it.tag is PlayTag.Action }
            config = applyMove(config, aliceMove)

            // Finalize frontier to advance to Bob's yield
            config = applyMove(config, Label.FinalizeFrontier)
            config = Configuration(config.frontier, config.history, emptyMap()) // Reset partial after checking

            // Bob acts
            val moves2 = semantics.enabledMoves(config)
            val bobMove = moves2.filterIsInstance<Label.Play>().first { it.role == bob && it.tag is PlayTag.Action }
            config = applyMove(config, bobMove)

            // Partial should contain Bob's delta
            config.partial shouldBe bobMove.delta
        }

        "preserves frontier and history" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            val originalFrontier = config.frontier
            val originalHistory = config.history

            val moves = semantics.enabledMoves(config)
            val playMove = moves.filterIsInstance<Label.Play>().first()

            val nextConfig = applyMove(config, playMove)

            nextConfig.frontier shouldBe originalFrontier
            nextConfig.history shouldBe originalHistory
        }
    }

    "applyMove FinalizeFrontier" - {

        "finalize partial to history" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice acts
            val moves = semantics.enabledMoves(config)
            val playMove = moves.filterIsInstance<Label.Play>().first()
            config = applyMove(config, playMove)

            val partialBeforeFinalization = config.partial

            // Finalize frontier
            val nextConfig = applyMove(config, Label.FinalizeFrontier)

            // History should contain the finalized partial
            val aliceField = FieldRef(alice, VarId("x"))
            val valueInHistory = nextConfig.history.get(aliceField)
            val valueInPartial = partialBeforeFinalization[aliceField]

            valueInHistory shouldBe valueInPartial
        }

        "clears partial" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Alice acts
            val moves = semantics.enabledMoves(config)
            val playMove = moves.filterIsInstance<Label.Play>().first()
            config = applyMove(config, playMove)

            // Partial should be non-empty
            config.partial.isEmpty() shouldBe false

            // Finalize frontier
            val nextConfig = applyMove(config, Label.FinalizeFrontier)

            // Partial should be cleared
            nextConfig.partial.isEmpty() shouldBe true
        }

        "advances frontier" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            val enabledBeforeFinalization = config.frontier.enabled()

            // Alice acts
            val moves = semantics.enabledMoves(config)
            val playMove = moves.filterIsInstance<Label.Play>().first()
            config = applyMove(config, playMove)

            // Finalize frontier
            val nextConfig = applyMove(config, Label.FinalizeFrontier)

            // Frontier should have advanced (different enabled actions or terminal)
            val enabledAfterFinalization = nextConfig.frontier.enabled()
            val frontierAdvanced = (enabledAfterFinalization != enabledBeforeFinalization) || nextConfig.isTerminal()
            frontierAdvanced shouldBe true
        }
    }

    "stepping through complete game" - {

        "reaches correct terminal for simple game" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())

            // Step through until terminal
            var steps = 0
            while (!config.isTerminal() && steps < 10) {
                val moves = semantics.enabledMoves(config)
                if (moves.isEmpty()) break

                // Take first move
                val move = moves.first()
                config = applyMove(config, move)

                steps++
            }

            // Should reach terminal
            config.isTerminal() shouldBe true
            // Should have taken some steps
            (steps > 0) shouldBe true
        }

        "preserves history through multiple frontiers" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                yield Alice(y: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())

            // Step through first yield
            repeat(3) {
                val moves = semantics.enabledMoves(config)
                if (moves.isEmpty()) return@repeat
                val move = moves.first()
                config = applyMove(config, move)
            }

            // History should contain x
            val xField = FieldRef(alice, VarId("x"))
            val xValue = config.history.get(xField)
            xValue shouldBe IrVal.BoolVal(true)

            // Continue to second yield
            repeat(3) {
                val moves = semantics.enabledMoves(config)
                if (moves.isEmpty()) return@repeat
                val move = moves.first()
                config = applyMove(config, move)
            }

            // History should still contain x and now y
            val yField = FieldRef(alice, VarId("y"))
            val yValue = config.history.get(yField)

            xValue shouldBe IrVal.BoolVal(true)
            yValue shouldBe IrVal.BoolVal(true)
        }

        "quit moves work correctly" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)

            var config = Configuration(FrontierMachine.from(ir.dag), History())
            config = Configuration(config.frontier.resolveEnabled(), config.history, emptyMap())

            // Take quit move
            val moves = semantics.enabledMoves(config)
            val quitMove = moves.filterIsInstance<Label.Play>().first { it.tag is PlayTag.Quit }
            config = applyMove(config, quitMove)

            // Partial should contain Quit value
            val xField = FieldRef(alice, VarId("x"))
            config.partial[xField] shouldBe IrVal.Quit

            // Finalize the quit
            config = applyMove(config, Label.FinalizeFrontier)

            // History should show Alice quit
            config.history.quit(alice) shouldBe true
        }
    }
})

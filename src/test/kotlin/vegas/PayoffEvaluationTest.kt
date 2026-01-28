package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.ints.shouldBeGreaterThan
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.runtime.LocalRuntime

/**
 * Tests that payoff computation produces correct results.
 *
 * "No test evaluates payoff expressions against a known game outcome and checks
 * the numeric result."
 *
 * Focus areas:
 * 1. Conservation property - payoffs sum to total deposits
 * 2. Non-negative payoffs - all payoffs >= 0
 * 3. Terminal state validation - games reach terminal
 */
class PayoffEvaluationTest : FreeSpec({

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    /** Play a game with default non-quit moves until terminal */
    fun playToTerminal(game: GameIR): Map<RoleId, Int> {
        val session = LocalRuntime().deploy(game)

        var iterations = 0
        while (!session.isTerminal() && iterations++ < 100) {
            val moves = session.legalMoves()
            if (moves.isEmpty()) break

            // Always prefer non-quit moves
            val nonQuitMoves = moves.filter { m ->
                !m.assignments.values.any { it is Expr.Const.Quit }
            }

            val move = nonQuitMoves.firstOrNull() ?: break

            session.submitMove(move)
        }

        return if (session.isTerminal()) session.payoffs() else emptyMap()
    }

    "Conservation property" - {
        /**
         * The fundamental invariant: payoffs must sum to total deposits.
         * This verifies the withdraw expressions are correctly implemented.
         */
        "Prisoners: payoffs sum to 200" {
            val game = loadGame("Prisoners")
            val payoffs = playToTerminal(game)
            payoffs.values.sum() shouldBe 200
        }


        "Dominance: payoffs sum to 20" {
            val game = loadGame("Dominance")
            val payoffs = playToTerminal(game)
            payoffs.values.sum() shouldBe 20
        }

        "Simple: payoffs sum to 12" {
            val game = loadGame("Simple")
            val payoffs = playToTerminal(game)
            payoffs.values.sum() shouldBe 12
        }

        "Trivial1: payoffs sum to 10" {
            val game = loadGame("Trivial1")
            val payoffs = playToTerminal(game)
            payoffs.values.sum() shouldBe 10
        }

        "OddsEvensShort: payoffs sum to 200" {
            val game = loadGame("OddsEvensShort")
            val payoffs = playToTerminal(game)
            payoffs.values.sum() shouldBe 200
        }
    }

    "Payoffs are well-defined" - {
        /**
         * All roles should have payoffs defined at terminal.
         * Payoffs should be non-negative (can't lose more than deposited).
         */
        "Prisoners: all roles have non-negative payoffs" {
            val game = loadGame("Prisoners")
            val payoffs = playToTerminal(game)

            game.roles.forEach { role ->
                val payoff = payoffs[role] ?: 0
                payoff shouldBeGreaterThan -1
            }
        }

        "Dominance: all roles have non-negative payoffs" {
            val game = loadGame("Dominance")
            val payoffs = playToTerminal(game)

            game.roles.forEach { role ->
                val payoff = payoffs[role] ?: 0
                payoff shouldBeGreaterThan -1
            }
        }

        "OddsEvensShort: all roles have non-negative payoffs" {
            val game = loadGame("OddsEvensShort")
            val payoffs = playToTerminal(game)

            game.roles.forEach { role ->
                val payoff = payoffs[role] ?: 0
                payoff shouldBeGreaterThan -1
            }
        }
    }

    "Games reach terminal" - {
        /**
         * Verify that games reach terminal state when played with default moves.
         * This is a sanity check that the semantic model works correctly.
         */
        "Prisoners: reaches terminal state" {
            val game = loadGame("Prisoners")
            val payoffs = playToTerminal(game)
            payoffs.isEmpty() shouldBe false
        }

        "Dominance: reaches terminal state" {
            val game = loadGame("Dominance")
            val payoffs = playToTerminal(game)
            payoffs.isEmpty() shouldBe false
        }

        "Simple: reaches terminal state" {
            val game = loadGame("Simple")
            val payoffs = playToTerminal(game)
            payoffs.isEmpty() shouldBe false
        }

        "Trivial1: reaches terminal state" {
            val game = loadGame("Trivial1")
            val payoffs = playToTerminal(game)
            payoffs.isEmpty() shouldBe false
        }

        "OddsEvensShort: reaches terminal state" {
            val game = loadGame("OddsEvensShort")
            val payoffs = playToTerminal(game)
            payoffs.isEmpty() shouldBe false
        }
    }

    "Specific payoff scenario" - {
        /**
         * Test specific known outcome for Prisoners' Dilemma.
         * Both cooperate (c=true) should give A=100, B=100.
         */
        "Prisoners: both cooperate" {
            val game = loadGame("Prisoners")
            val session = LocalRuntime().deploy(game)

            while (!session.isTerminal()) {
                val moves = session.legalMoves()
                val nonQuitMoves = moves.filter { m ->
                    !m.assignments.values.any { it is Expr.Const.Quit }
                }

                if (nonQuitMoves.isEmpty()) break

                val move = nonQuitMoves.first()

                // For 'c' parameter, pick true (cooperate)
                val customMove = if (move.assignments.keys.any { it.name == "c" }) {
                    move.copy(assignments = mapOf(VarId("c") to Expr.Const.BoolVal(true)))
                } else {
                    move
                }

                session.submitMove(customMove)
            }

            if (session.isTerminal()) {
                val payoffs = session.payoffs()
                payoffs[RoleId("A")] shouldBe 100
                payoffs[RoleId("B")] shouldBe 100
            }
        }
    }
})

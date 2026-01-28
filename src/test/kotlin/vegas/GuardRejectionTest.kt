package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldNotContain
import io.kotest.matchers.ints.shouldBeGreaterThan
import io.kotest.matchers.ints.shouldBeLessThan
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.runtime.LocalRuntime
import vegas.runtime.GameMove
import vegas.runtime.GameSession

/**
 * Tests that the semantic model correctly enforces guards.
 *
 * This addresses a bug where the TraceEnumerator only generates guard-satisfying assignments,
 * so guard-violating values are never tested for rejection.
 *
 * Rather than trying to submit illegal moves (which would require bypassing
 * the legalMoves() enumeration), we verify that the enumeration itself
 * correctly excludes guard-violating values.
 *
 * Equivalence classes tested:
 * 1. Inequality guards (where a != b) - MontyHall
 * 2. Domain guards - values are restricted to declared set
 * 3. Alldiff guards - TicTacToe
 */
class GuardRejectionTest : FreeSpec({

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    /** Play game until a specific parameter appears in legal moves */
    fun playUntilParam(session: GameSession, paramName: String): List<GameMove> {
        var iterations = 0
        while (!session.isTerminal() && iterations++ < 50) {
            val moves = session.legalMoves()
            val targetMoves = moves.filter { move ->
                move.assignments.keys.any { it.name == paramName } &&
                !move.assignments.values.any { it is Expr.Const.Quit }
            }
            if (targetMoves.isNotEmpty()) {
                return targetMoves
            }
            // Submit first non-quit move
            val move = moves.firstOrNull { m ->
                !m.assignments.values.any { it is Expr.Const.Quit }
            } ?: moves.firstOrNull() ?: break
            session.submitMove(move)
        }
        return emptyList()
    }

    /** Extract int values from moves for a specific parameter */
    fun extractIntValues(moves: List<GameMove>, paramName: String): List<Int> {
        return moves.flatMap { move ->
            move.assignments.entries
                .filter { it.key.name == paramName }
                .mapNotNull { entry ->
                    when (val v = entry.value) {
                        is Expr.Const.IntVal -> v.v
                        is Expr.Const.Hidden -> (v.inner as? Expr.Const.IntVal)?.v
                        else -> null
                    }
                }
        }.distinct().sorted()
    }

    "Domain guards" - {
        /**
         * Domain guards ensure parameter values are within the declared type.
         * For MontyHall's door={0,1,2}, all door parameters should only have values 0, 1, or 2.
         */
        "MontyHall: door type restricts to {0,1,2}" {
            val game = loadGame("MontyHall")
            val session = LocalRuntime().deploy(game)

            // Get to Host's car commit
            val carMoves = playUntilParam(session, "car")
            val carValues = extractIntValues(carMoves, "car")

            // Should only have valid door values
            carValues shouldBe listOf(0, 1, 2)
        }

        "TicTacToe: cell values restricted to declared domain" {
            val game = loadGame("TicTacToe")
            val session = LocalRuntime().deploy(game)

            // Get to X's c1 move
            val c1Moves = playUntilParam(session, "c1")
            val c1Values = extractIntValues(c1Moves, "c1")

            // TicTacToe uses d={0..8} for cells (9 cells)
            c1Values.forEach { it shouldBeGreaterThan -1 }
            c1Values.forEach { it shouldBeLessThan 9 }
            c1Values.size shouldBeGreaterThan 0
        }
    }

    "Inequality guards" - {
        /**
         * MontyHall: Host.goat != Guest.d
         * After Guest picks a door, Host's goat options should exclude that door.
         */
        "MontyHall: goat options exclude Guest's door" {
            val game = loadGame("MontyHall")
            val session = LocalRuntime().deploy(game)

            // Play through to goat selection, with Guest picking door 0
            var iterations = 0
            var guestPickedDoor: Int? = null

            while (!session.isTerminal() && iterations++ < 50) {
                val moves = session.legalMoves()
                val goatMoves = moves.filter { move ->
                    move.assignments.keys.any { it.name == "goat" } &&
                    !move.assignments.values.any { it is Expr.Const.Quit }
                }

                if (goatMoves.isNotEmpty()) {
                    // Verify goat options don't include Guest's picked door
                    val goatValues = extractIntValues(goatMoves, "goat")

                    if (guestPickedDoor != null) {
                        goatValues shouldNotContain guestPickedDoor
                    }

                    // goatValues should have fewer than 3 options (one is excluded)
                    goatValues.size shouldBeLessThan 3
                    break
                }

                // Submit a move, tracking Guest's door choice
                val move = moves.firstOrNull { m ->
                    !m.assignments.values.any { it is Expr.Const.Quit }
                } ?: break

                // If this is Guest's d choice, pick door 0 and remember it
                if (move.assignments.keys.any { it.name == "d" }) {
                    val doorMove = move.copy(
                        assignments = mapOf(VarId("d") to Expr.Const.IntVal(0))
                    )
                    session.submitMove(doorMove)
                    guestPickedDoor = 0
                } else {
                    session.submitMove(move)
                }
            }

            // Verify we found goat moves
            guestPickedDoor shouldBe 0
        }
    }

    "Alldiff guards" - {
        /**
         * TicTacToe: alldiff(X.c1, O.c1, ...) ensures no cell reuse.
         * After X picks a cell, O's options for the same move should exclude it.
         */
        "TicTacToe: second player cannot reuse first player's cell" {
            val game = loadGame("TicTacToe")
            val session = LocalRuntime().deploy(game)

            // Get to X's c1 move and pick cell 0
            val xMoves = playUntilParam(session, "c1")
            val xMove = xMoves.find { move ->
                extractIntValues(listOf(move), "c1").contains(0)
            }

            if (xMove != null) {
                session.submitMove(xMove.copy(
                    assignments = mapOf(VarId("c1") to Expr.Const.IntVal(0))
                ))

                // Get O's c1 options
                val oMoves = session.legalMoves().filter { move ->
                    move.assignments.keys.any { it.name == "c1" } &&
                    !move.assignments.values.any { it is Expr.Const.Quit }
                }

                val oValues = extractIntValues(oMoves, "c1")

                // O should not be able to pick 0 (alldiff constraint)
                oValues shouldNotContain 0

                // O should still have options
                oValues.size shouldBeGreaterThan 0
            }
        }
    }
})

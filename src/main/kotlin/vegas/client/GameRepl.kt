package vegas.client

import vegas.RoleId
import vegas.VarId
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Visibility
import vegas.runtime.*
import java.io.BufferedReader
import java.io.PrintStream

/**
 * Interactive REPL for playing Vegas games in the terminal.
 *
 * Hot-seat multiplayer: all roles play from the same terminal, taking turns.
 * The REPL prompts for moves, handles parameter input, and manages
 * commit-reveal internally (prompts for plain values, wraps in Hidden).
 */
class GameRepl(
    private val client: GameClient,
    private val game: GameIR,
    private val input: BufferedReader = System.`in`.bufferedReader(),
    private val output: PrintStream = System.out,
) {
    fun run() {
        output.println("=== Vegas Game: ${game.name} ===")
        output.println("Roles: ${(game.roles + game.chanceRoles).joinToString(", ")}")
        output.println()

        while (!client.isTerminal) {
            val state = client.describeState()
            if (state.isTerminal || state.currentMoves.isEmpty()) break

            output.print(MoveFormatter.format(state))
            output.println()

            // Collect moves from each role that has moves available
            for (roleState in state.roleStates) {
                if (client.isTerminal) break

                val moves = roleState.moves
                if (moves.isEmpty()) continue

                // If all moves for this role are zero-param (joins), auto-submit them
                val allZeroParam = moves.all { it.paramDomains.isEmpty() }
                if (allZeroParam) {
                    for (move in moves) {
                        output.println("> ${move.description}")
                        client.submitMove(move.index)
                    }
                    continue
                }

                // If there are prefilled assignments (from trace enumeration), submit directly
                val allPrefilled = moves.all { it.prefilledAssignments != null }
                if (allPrefilled) {
                    // These are fully determined moves (e.g., reveal)
                    for (move in moves) {
                        output.println("> ${move.description}")
                        client.submitMove(move.index)
                    }
                    continue
                }

                // Interactive: prompt for move selection
                val move = if (moves.size == 1) {
                    moves[0]
                } else {
                    promptMoveChoice(roleState.role, moves)
                }

                if (move.paramDomains.isEmpty()) {
                    client.submitMove(move.index)
                } else {
                    val values = promptParameters(move)
                    val assignments = buildAssignments(move, values)
                    client.submitMove(GameMove(
                        actionId = move.actionId,
                        role = move.role,
                        visibility = move.visibility,
                        assignments = assignments,
                    ))
                }
            }
        }

        output.println()
        output.println(MoveFormatter.formatPayoffs(client.payoffs()))
    }

    private fun promptMoveChoice(role: RoleId, moves: List<MoveOption>): MoveOption {
        while (true) {
            output.print("$role, choose move [${moves.map { it.index + 1 }.joinToString("/")}]: ")
            output.flush()
            val line = input.readLine()?.trim() ?: break
            val choice = line.toIntOrNull()
            if (choice != null) {
                val found = moves.find { it.index + 1 == choice }
                if (found != null) return found
            }
            output.println("Invalid choice. Try again.")
        }
        return moves.first() // fallback
    }

    private fun promptParameters(move: MoveOption): Map<VarId, Any> {
        val result = mutableMapOf<VarId, Any>()

        for (pd in move.paramDomains) {
            val value = when {
                pd.values != null && pd.values.all { it is Boolean } -> {
                    promptBool(move.role, pd.name)
                }
                pd.values != null -> {
                    promptFromDomain(move.role, pd.name, pd.values)
                }
                else -> {
                    promptInt(move.role, pd.name)
                }
            }
            result[pd.name] = value
        }
        return result
    }

    private fun promptBool(role: RoleId, name: VarId): Boolean {
        while (true) {
            output.print("$role.$name (true/false): ")
            output.flush()
            val line = input.readLine()?.trim()?.lowercase() ?: return false
            when (line) {
                "true", "t", "1", "yes", "y" -> return true
                "false", "f", "0", "no", "n" -> return false
                else -> output.println("Enter true or false.")
            }
        }
    }

    private fun promptFromDomain(role: RoleId, name: VarId, values: List<Any>): Any {
        while (true) {
            output.print("$role.$name (${values.joinToString(", ")}): ")
            output.flush()
            val line = input.readLine()?.trim() ?: return values.first()
            val intVal = line.toIntOrNull()
            if (intVal != null && intVal in values.map { (it as? Int) ?: -1 }) {
                return intVal
            }
            // Try boolean
            if (values.any { it is Boolean }) {
                when (line.lowercase()) {
                    "true", "t" -> return true
                    "false", "f" -> return false
                }
            }
            output.println("Invalid. Choose from: ${values.joinToString(", ")}")
        }
    }

    private fun promptInt(role: RoleId, name: VarId): Int {
        while (true) {
            output.print("$role.$name (integer): ")
            output.flush()
            val line = input.readLine()?.trim() ?: return 0
            val v = line.toIntOrNull()
            if (v != null) return v
            output.println("Enter a valid integer.")
        }
    }

    private fun buildAssignments(move: MoveOption, values: Map<VarId, Any>): Map<VarId, Expr.Const> {
        return values.map { (varId, value) ->
            val base = when (value) {
                is Boolean -> Expr.Const.BoolVal(value)
                is Int -> Expr.Const.IntVal(value)
                else -> error("Unsupported value type: ${value::class}")
            }
            val wrapped = if (move.visibility == Visibility.COMMIT) {
                Expr.Const.Hidden(base)
            } else {
                base
            }
            varId to wrapped
        }.toMap()
    }
}

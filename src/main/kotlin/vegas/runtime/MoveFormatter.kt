package vegas.runtime

import vegas.ir.Type
import vegas.ir.Visibility

/**
 * Renders [MoveOption] lists as numbered text for display in a CLI REPL.
 */
object MoveFormatter {

    /**
     * Format a [GameState] for terminal display.
     */
    fun format(state: GameState): String = buildString {
        if (state.isTerminal) {
            appendLine("Game over.")
            return@buildString
        }

        for (roleState in state.roleStates) {
            appendLine("${roleState.role}:")
            for (move in roleState.moves) {
                append("  [${move.index + 1}] ${move.description}")
                // Show domain hints for parameterized moves
                if (move.paramDomains.isNotEmpty() && move.prefilledAssignments == null) {
                    val hints = move.paramDomains.mapNotNull { pd ->
                        when {
                            pd.values != null && pd.values.size <= 8 ->
                                "${pd.name} in {${pd.values.joinToString(", ")}}"
                            pd.type is Type.IntType ->
                                "${pd.name}: enter integer"
                            else -> null
                        }
                    }
                    if (hints.isNotEmpty()) {
                        append("  -- ${hints.joinToString("; ")}")
                    }
                }
                if (move.prefilledAssignments != null) {
                    val vals = move.prefilledAssignments.entries.joinToString(", ") { (k, v) -> "$k=$v" }
                    append("  [$vals]")
                }
                if (move.visibility == Visibility.COMMIT) {
                    append("  (hidden)")
                }
                appendLine()
            }
        }
    }

    /**
     * Format payoffs for terminal display.
     */
    fun formatPayoffs(payoffs: Map<vegas.RoleId, Int>): String = buildString {
        appendLine("Final payoffs:")
        for ((role, amount) in payoffs.entries.sortedBy { it.key.name }) {
            appendLine("  $role -> $amount")
        }
    }
}

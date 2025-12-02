package vegas.backend.gambit

import vegas.RoleId
import vegas.dag.FrontierMachine
import vegas.ir.ActionDag
import vegas.ir.ActionId

/**
 * A configuration in the game LTS.
 *
 * Represents the complete state at a point in game execution:
 *
 * From a configuration Γ we can derive:
 *  - enabled(Γ) = frontier.enabled()
 *  - per-role views via views(role)
 *  - which roles have acted in the current frontier
 *
 * @param frontier Which actions are currently enabled (the DAG frontier)
 * @param history The committed global truth (stack of frontier slices)
 * @param partial Accumulated assignments for the current frontier (not yet committed)
 */
internal data class Configuration(
    val frontier: FrontierMachine<ActionId>,
    val history: History,
    val partial: FrontierAssignmentSlice = emptyMap()
) {
    /** Check if this configuration is terminal (no more actions possible) */
    fun isTerminal(): Boolean = frontier.isComplete()

    /** Get the set of currently enabled actions */
    fun enabled(): Set<ActionId> = frontier.enabled()

    /**
     * Group enabled actions by their owner role.
     * Used for enumerating moves per role.
     */
    fun actionsByRole(dag: ActionDag): Map<RoleId, List<ActionId>> =
        enabled().groupBy { dag.owner(it) }

    /**
     * Roles that have parameters to assign in the current frontier.
     * A role with no parameters in this frontier doesn't need to "act".
     */
    fun rolesWithParams(dag: ActionDag): Set<RoleId> =
        actionsByRole(dag)
            .filterValues { actions -> actions.any { dag.params(it).isNotEmpty() } }
            .keys

    /**
     * Check if a role has already acted in the current partial frontier.
     *
     * A role that has already acted gets no more moves in this frontier.
     * This is checked by enabledMoves.
     */
    fun hasActed(role: RoleId): Boolean =
        partial.keys.any { it.owner == role }
}

/**
 * Construct per-role views from a configuration.
 *
 * Each role sees a redacted version of the history where:
 * - Their own Hidden values are unwrapped to actual values
 * - Others' Hidden values appear as Opaque
 *
 * This implements perfect recall: each role's view contains the full
 * observable past, built by replaying the history stack with per-slice
 * redaction.
 *
 * Note: This is computed on-demand rather than stored in Configuration
 * to save memory in large trees (partial is frequently updated).
 */
internal fun Configuration.views(allRoles: Set<RoleId>): HistoryViews {
    // Unwind the history stack to chronological order (root -> leaf)
    val slices = ArrayDeque<FrontierAssignmentSlice>()
    var curr: History? = history

    while (curr != null && curr.past != null) {
        slices.addFirst(curr.lastFrontier)
        curr = curr.past
    }

    // Replay history with per-role redaction
    // Use the existing `redacted` function from GameState.kt (do not reimplement!)
    val currentViews = allRoles.associateWith { History() }.toMutableMap()
    for (slice in slices) {
        for (role in allRoles) {
            val view = currentViews.getValue(role)
            // Use existing redacted function and History.with operator
            currentViews[role] = view with redacted(slice, role)
        }
    }

    return currentViews
}

package vegas.semantics

import vegas.RoleId
import vegas.dag.FrontierMachine
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.GameIR

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
 * @param partialFrontierAssignment Accumulated assignments for the current frontier (not yet committed)
 */
data class Configuration(
    val frontier: FrontierMachine<ActionId>,
    val history: History,
    val partialFrontierAssignment: FrontierAssignmentSlice = emptyMap()
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
        partialFrontierAssignment.keys.any { it.owner == role }

    companion object {
        fun initial(game: GameIR): Configuration {
            return Configuration(
                frontier = FrontierMachine.from(game.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
        }
    }
}

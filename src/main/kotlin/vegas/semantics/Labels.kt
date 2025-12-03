package vegas.semantics

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.Expr.Const
import vegas.ir.Expr.Const.Quit

/**
 * Labels for the game LTS.
 *
 * Two kinds of transitions:
 * - [Play]: A role makes a choice (explicit action or quit)
 * - [FinalizeFrontier]: Internal step that finalizes accumulated partial frontier
 */
internal sealed class Label {
    /**
     * Player move: a role assigns values to their parameters.
     *
     * @property role The role making the choice
     * @property delta The field assignments (FieldRef -> Expr.Const mapping)
     * @property tag Whether this is an explicit action or quit move
     */
    data class Play(
        val role: RoleId,
        val delta: FrontierAssignmentSlice,
        val tag: PlayTag
    ) : Label()

    /**
     * Internal frontier finalization step (τ).
     *
     * Enabled when all required roles have acted in the current frontier.
     * Finalizes [Configuration.partialFrontierAssignment] to [Configuration.history] and advances
     * to the next frontier.
     */
    object FinalizeFrontier : Label()
}

/**
 * Tag identifying the kind of play move.
 */
internal sealed class PlayTag {
    /**
     * Explicit action: role assigns parameters for this action.
     * @property actionId The action being executed
     */
    data class Action(val actionId: ActionId) : PlayTag()

    /**
     * Quit move: role abandons (sets all their parameters to Quit).
     * Strategic players only; chance roles never quit.
     */
    object Quit : PlayTag()
}

/**
 * Create a frontier slice where all parameters of the given actions are set to [Expr.Const.Quit].
 * This represents the "quit" choice where a strategic player opts out of all actions at a frontier.
 */
internal fun allParametersQuit(dag: ActionDag, role: RoleId, actions: List<ActionId>): FrontierAssignmentSlice =
    actions.flatMap { actionId ->
        dag.params(actionId).map { FieldRef(role, it.name) to Expr.Const.Quit }
    }.toMap()

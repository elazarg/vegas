package vegas.backend.gambit

import vegas.RoleId
import vegas.ir.ActionId

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
     * @property delta The field assignments (FieldRef -> IrVal mapping)
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

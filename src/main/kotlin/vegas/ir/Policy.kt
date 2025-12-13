package vegas.ir

import vegas.FieldRef
import vegas.RoleId

/**
 * Defines the semantics of abandonment (quitting) in the game.
 *
 * This interface allows decoupling the core game logic from the specific strategy
 * used to handle player timeouts or explicit quits.
 */
interface QuitPolicy {
    /**
     * Determines the effect of a role quitting on the game state (the delta).
     *
     * @param role The role that is quitting.
     * @param pendingActions The actions for this role in the current frontier.
     * @param dag The action DAG (to resolve parameters).
     * @return A map of field assignments to apply to the history (e.g., setting fields to Quit or substitute values).
     */
    fun getQuitDelta(
        role: RoleId,
        pendingActions: List<ActionId>,
        dag: ActionDag
    ): Map<FieldRef, Expr.Const>

    /**
     * Resolves a value read from history during expression evaluation.
     *
     * This allows the policy to intercept reads of fields owned by players who have quit
     * (or other conditions) and substitute values (e.g. treating Quit as null, or a default value).
     *
     * @param value The raw value found in history (may be Expr.Const.Quit, Hidden, or a concrete value).
     * @param field The field being read.
     * @return The resolved value to be used in the expression, or null if undefined.
     */
    fun resolveRead(value: Expr.Const?, field: FieldRef): Expr.Const?
}

package vegas.semantics

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.ir.Expr

/**
 * A map from field references to values representing one layer of action writes.
 * This is the atomic unit of state update in the frontier-based game tree construction.
 */
typealias FrontierAssignmentSlice = Map<FieldRef, Expr.Const>

/**
 * Visible snapshot to 'who' at a given frontier: others' Hidden appear as Opaque.
 * Abandonment is represented by Expr.Const.Quit and is never hidden.
 *
 * This implements the information-hiding semantics:
 * - Own fields: player sees actual values (unwraps Hidden)
 * - Others' hidden fields: player sees Opaque (commitment made, value unknown)
 * - Others' public fields and Quit: pass through unchanged
 *
 * @param messages The frontier slice to redact
 * @param who The role for whom this view is being constructed
 * @return Redacted frontier slice as seen by [who]
 */
fun redacted(messages: FrontierAssignmentSlice, who: RoleId): FrontierAssignmentSlice =
    messages.mapValues { (fieldRef, v) ->
        val (r, _) = fieldRef
        if (r == who) {
            if (v is Expr.Const.Hidden) v.inner else v
        } else when (v) {
            is Expr.Const.Hidden -> Expr.Const.Opaque  // Others see that commitment happened, not the value
            else -> v  // Quit and other values pass through
        }
    }

/**
 * A stack of frontier slices representing the history of action writes.
 *
 * This plays a dual role:
 * - **Global state**: The actual history of what happened (all values concrete)
 * - **Player knowledge**: A redacted view of history (hidden values appear as Opaque)
 *
 * The stack structure implements perfect recall: each new frontier slice is pushed
 * on top of the previous state, preserving the complete history of observations.
 *
 * @property lastFrontier The most recent frontier slice
 * @property past The previous state (null for initial empty state)
 */
data class History(
    val lastFrontier: FrontierAssignmentSlice = emptyMap(),
    val past: History? = null,
) {
    /**
     * Look up a field's value by searching backwards through the history.
     * Returns the most recent write to this field, or [Expr.Const.Quit] if never written.
     */
    fun get(f: FieldRef): Expr.Const =
        lastFrontier[f] ?: (past?.get(f) ?: Expr.Const.Quit)

    /**
     * Push a new frontier slice onto the history stack.
     * Returns a new History with this state as the past.
     */
    infix fun with(newFrontier: FrontierAssignmentSlice): History =
        History(newFrontier, this)
}

/**
 * Per-role knowledge: redacted views of history for information set construction.
 * Each role's knowledge is an History where others' hidden values appear as Opaque.
 */
typealias HistoryViews = Map<RoleId, History>

/**
 * Check if a role has ever abandoned (written [Expr.Const.Quit]) anywhere in the history.
 * Once a role quits, they have no more legal choices (they're out of the game).
 *
 * @param role The role to check
 * @return true if this role has written Quit to any of their fields
 */
fun History.quit(role: RoleId): Boolean =
    lastFrontier.any { (field, v) -> field.owner == role && v == Expr.Const.Quit } ||
            (past?.quit(role) ?: false)

/**
 * Convert a packet (map from parameter names to values) into a frontier slice.
 * This adds the role information to create FieldRefs.
 *
 * @param role The role performing these actions
 * @param pkt The packet of parameter assignments
 * @return A frontier slice mapping FieldRef to Expr.Const
 */
fun toFrontierMap(role: RoleId, pkt: Map<VarId, Expr.Const>): FrontierAssignmentSlice =
    pkt.mapKeys { (v, _) -> FieldRef(role, v) }

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
fun reconstructViews(globalHistory: History, roles: Set<RoleId>): HistoryViews {
    // 1. Unwind the stack to get slices in chronological order (Root -> Leaf)
    val slices = ArrayDeque<FrontierAssignmentSlice>()
    var curr: History? = globalHistory

    // Assumes History has a 'parent' or 'prev' field and a 'slice' field
    while (curr != null && curr.past != null) {
        slices.addFirst(curr.lastFrontier)
        curr = curr.past
    }

    // 2. Replay history to build views
    // Start with empty history for everyone
    val currentViews = roles.associateWith { History() }.toMutableMap()

    for (slice in slices) {
        for (role in roles) {
            val view = currentViews.getValue(role)
            // Reuse the existing 'redacted' logic used in exploreJointChoices
            currentViews[role] = view with redacted(slice, role)
        }
    }
    return currentViews
}

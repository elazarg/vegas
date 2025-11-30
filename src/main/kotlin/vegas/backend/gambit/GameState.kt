package vegas.backend.gambit

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId

/**
 * A map from field references to values representing one layer of action writes.
 * This is the atomic unit of state update in the frontier-based game tree construction.
 */
internal typealias FrontierSlice = Map<FieldRef, IrVal>

/**
 * Visible snapshot to 'who' at a given frontier: others' Hidden appear as Opaque.
 * Bail/abandonment is represented by IrVal.Quit and is never hidden.
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
internal fun redacted(messages: FrontierSlice, who: RoleId): FrontierSlice =
    messages.mapValues { (fieldRef, v) ->
        val (r, _) = fieldRef
        if (r == who) {
            if (v is IrVal.Hidden) v.inner else v
        } else when (v) {
            is IrVal.Hidden -> IrVal.Opaque  // Others see that commitment happened, not the value
            else -> v  // Quit (bail) and other values pass through
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
internal data class Infoset(
    val lastFrontier: FrontierSlice = emptyMap(),
    val past: Infoset? = null,
) {
    /**
     * Look up a field's value by searching backwards through the history.
     * Returns the most recent write to this field, or [IrVal.Quit] if never written.
     */
    fun get(f: FieldRef): IrVal =
        lastFrontier[f] ?: (past?.get(f) ?: IrVal.Quit)

    /**
     * Push a new frontier slice onto the history stack.
     * Returns a new Infoset with this state as the past.
     */
    infix fun with(newFrontier: FrontierSlice): Infoset =
        Infoset(newFrontier, this)
}

/**
 * Global game state: concrete history of what actually happened.
 */
internal typealias State = Infoset

/**
 * Per-role knowledge: redacted views of history for information set construction.
 * Each role's knowledge is an Infoset where others' hidden values appear as Opaque.
 */
internal typealias KnowledgeMap = Map<RoleId, Infoset>

/**
 * Check if a role has ever bailed (written [IrVal.Quit]) anywhere in the history.
 * Once a role bails, they have no more legal choices (they're out of the game).
 *
 * @param role The role to check
 * @return true if this role has written Quit to any of their fields
 */
internal fun Infoset.quit(role: RoleId): Boolean =
    lastFrontier.any { (field, v) -> field.role == role && v == IrVal.Quit } ||
            (past?.quit(role) ?: false)

/**
 * Convert a packet (map from parameter names to values) into a frontier slice.
 * This adds the role information to create FieldRefs.
 *
 * @param role The role performing these actions
 * @param pkt The packet of parameter assignments
 * @return A frontier slice mapping FieldRef to IrVal
 */
internal fun toFrontierMap(role: RoleId, pkt: Map<VarId, IrVal>): FrontierSlice =
    pkt.mapKeys { (v, _) -> FieldRef(role, v) }

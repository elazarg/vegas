package vegas.backend.clarity

import vegas.RoleId
import vegas.semantics.Label

/**
 * An explicit state machine (ESM) optimized for Clarity generation.
 *
 * Similar to LightningProtocol but adapted for on-chain state.
 *
 * @param name Game name.
 * @param roles List of roles in canonical order.
 * @param states Map of StateId to State.
 * @param rootStateId The initial state ID.
 * @param totalPot The total funds locked (sum of all join deposits).
 */
internal data class ClarityProtocol(
    val name: String,
    val roles: List<RoleId>,
    val states: Map<Int, ClarityState>,
    val rootStateId: Int,
    val totalPot: Long
)

/**
 * A state in the Clarity state machine.
 */
internal data class ClarityState(
    val id: Int,

    /**
     * The role expected to act in this state.
     * Null if this is a terminal state (or possibly a forced-abort state being resolved, though usually we compile those away).
     */
    val activePlayer: RoleId?,

    /**
     * Transitions from this state triggered by actions.
     */
    val transitions: List<ClarityTransition>,

    /**
     * If the active player times out (or if this is a terminal state),
     * these are the balances to distribute.
     */
    val abortBalance: Map<RoleId, Long>,

    /**
     * How long (in seconds or block height) to wait before allowing timeout.
     * Derived from configuration or annotations.
     */
    val timeoutDelta: Long
)

internal data class ClarityTransition(
    val label: Label,
    val nextStateId: Int
)

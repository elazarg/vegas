package vegas.backend.bitcoin

import vegas.RoleId
import vegas.semantics.Label

/**
 * A fully expanded, verified explicit state machine (ESM) for a Lightning-compatible game.
 *
 * **Supported Game Fragment:**
 * 1. **Two-Player:** Exactly two strategic roles (A and B).
 *
 * 2. **Serializable Execution:** The state machine enforces a deterministic turn-based ordering.
 *    - Games with simultaneous moves are supported via commit-reveal expansion in the IR.
 *    - The IR's commit-reveal transformation ensures any topological ordering is strategically
 *      equivalent (committed values are hidden, so ordering doesn't reveal information).
 *    - Each protocol state has exactly one active player, with remaining players acting in
 *      subsequent states within the same logical frontier.
 *
 * 3. **Distribution Semantics:**
 *    - At every terminal / abort outcome, the game's payoffs for roleA and roleB are interpreted
 *      as *withdrawal amounts* from a fixed Lightning pot `totalPot`.
 *    - Withdrawals must be non-negative and their sum must not exceed `totalPot`.
 *    - The backend does NOT enforce winner-takes-all; arbitrary deterministic splits are allowed.
 *
 * 4. **Deterministic Abort:**
 *    - Every strategic state must have an explicit `Quit` move for the active player.
 *    - Quitting must lead deterministically (via `FinalizeFrontier` and cascading quits) to a
 *      terminal state whose withdrawals define `abortBalance`.
 *
 * 5. **System Moves:**
 *    - Only `Label.FinalizeFrontier` is supported. Games with `Chance` or other internal steps are rejected.
 */
internal data class LightningProtocol(
    val name: String,
    val roleA: RoleId,
    val roleB: RoleId,
    val totalPot: Long, // Total satoshis locked in the channel
    val rootStateId: StateId,
    val states: Map<StateId, ProtocolState>
)

typealias StateId = Int

/**
 * A node in the Verified State Machine.
 */
internal data class ProtocolState(
    val id: StateId,

    /**
     * The channel distribution required to safely be in this state.
     *
     * Semantics:
     * - **Terminal:** The final withdrawal amounts for roleA and roleB.
     * - **Strategic:** The amounts that will apply if `activePlayer` forfeits (Quits) right now.
     * - **Forced Abort:** The amounts after simulating pending forced quits.
     */
    val abortBalance: BalanceSplit,

    /**
     * The player who must provide the next input.
     * Null if and only if this is a terminal / forced-abort state (no further strategic actions).
     */
    val activePlayer: RoleId?,

    /**
     * Valid transitions to next states.
     * Empty if `activePlayer` is null.
     * Contains only strategic moves (Play excluding Quit).
     */
    val transitions: List<ProtocolTransition>
)

internal data class BalanceSplit(val amountA: Long, val amountB: Long)

internal data class ProtocolTransition(
    val label: Label,
    val nextStateId: StateId
)

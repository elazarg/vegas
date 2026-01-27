package vegas.runtime

import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Visibility

/**
 * A move in the game: a role submitting values for one action.
 *
 * @property actionId The DAG action being executed
 * @property role The role making the move
 * @property visibility COMMIT, REVEAL, or PUBLIC
 * @property assignments Field values being submitted (param name -> value)
 */
data class GameMove(
    val actionId: ActionId,
    val role: RoleId,
    val visibility: Visibility,
    val assignments: Map<VarId, Expr.Const>,
)

/**
 * A session representing a deployed game instance.
 * Provides the interface for playing through a game.
 */
interface GameSession {
    /** All legal moves at the current game state. */
    fun legalMoves(): List<GameMove>

    /** Submit a move. Throws if the move is illegal. */
    fun submitMove(move: GameMove)

    /** Whether the game has reached a terminal state. */
    fun isTerminal(): Boolean

    /**
     * Compute payoffs for each role at the current (terminal) state.
     * Returns map from role -> payout amount (in wei for Ethereum, abstract units for local).
     * Should only be called when [isTerminal] returns true.
     */
    fun payoffs(): Map<RoleId, Int>
}

/**
 * Abstraction over game execution environments.
 * Implementations may run games locally (in-memory semantics) or
 * on an Ethereum node (deployed Solidity contract).
 */
interface GameRuntime {
    /** Deploy/initialize a game and return a session for playing it. */
    fun deploy(game: GameIR): GameSession
}

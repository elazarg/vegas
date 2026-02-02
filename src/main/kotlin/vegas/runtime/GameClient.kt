package vegas.runtime

import vegas.RoleId
import vegas.VarId
import vegas.ir.*

/**
 * High-level API for driving a game programmatically.
 *
 * Wraps a [GameSession] and provides a human-friendly interface:
 * - [describeState] returns structured state with legal moves grouped by role
 * - [submitMove] by index or by explicit values
 * - [payoffs] returns final payoffs when terminal
 *
 * Runtime-agnostic: works with [LocalRuntime] or any other [GameSession].
 */
class GameClient(
    private val game: GameIR,
    private val session: GameSession,
) {
    /** Structured description of the current game state. */
    fun describeState(): GameState {
        if (session.isTerminal()) {
            return GameState(
                isTerminal = true,
                roleStates = emptyList(),
                currentMoves = emptyList(),
            )
        }

        val moves = session.legalMoves()
        val indexed = moves.mapIndexed { idx, move -> toMoveOption(idx, move) }
        val byRole = indexed.groupBy { it.role }

        val roleStates = byRole.map { (role, roleMoves) ->
            RoleState(role = role, moves = roleMoves)
        }

        return GameState(
            isTerminal = false,
            roleStates = roleStates,
            currentMoves = indexed,
        )
    }

    /** Submit a move by its index from the current [describeState] move list. */
    fun submitMove(moveIndex: Int) {
        val moves = session.legalMoves()
        require(moveIndex in moves.indices) {
            "Move index $moveIndex out of range [0, ${moves.size})"
        }
        session.submitMove(moves[moveIndex])
    }

    /** Submit a move with explicit parameter values. */
    fun submitMove(role: RoleId, actionId: ActionId, values: Map<VarId, Any>) {
        val meta = game.dag.meta(actionId)
        val assignments = values.mapValues { (_, v) -> toConst(v, meta.kind) }
        session.submitMove(GameMove(
            actionId = actionId,
            role = role,
            visibility = meta.kind,
            assignments = assignments,
        ))
    }

    /** Submit a raw [GameMove] directly. */
    fun submitMove(move: GameMove) {
        session.submitMove(move)
    }

    /** Whether the game has reached a terminal state. */
    val isTerminal: Boolean get() = session.isTerminal()

    /** Payoffs for each role (only valid when [isTerminal] is true). */
    fun payoffs(): Map<RoleId, Int> = session.payoffs()

    private fun toMoveOption(index: Int, move: GameMove): MoveOption {
        val meta = game.dag.meta(move.actionId)
        val isJoin = meta.spec.join != null

        val description = buildString {
            append(move.role)
            if (isJoin) {
                val deposit = meta.spec.join.deposit.v
                append(": join")
                if (deposit > 0) append($$" (deposit $$$deposit)")
            } else {
                val kindLabel = when (meta.kind) {
                    Visibility.COMMIT -> "commit"
                    Visibility.REVEAL -> "reveal"
                    Visibility.PUBLIC -> "yield"
                }
                append(": $kindLabel")
                if (meta.spec.params.isNotEmpty()) {
                    val paramStr = meta.spec.params.joinToString(", ") { p ->
                        "${p.name}: ${typeLabel(p.type)}"
                    }
                    append(" $paramStr")
                }
            }
        }

        val paramDomains = meta.spec.params.map { p ->
            ParamDomain(
                name = p.name,
                type = p.type,
                values = enumerateDomain(p.type),
            )
        }

        return MoveOption(
            index = index,
            actionId = move.actionId,
            role = move.role,
            visibility = meta.kind,
            description = description,
            paramDomains = paramDomains,
            prefilledAssignments = move.assignments.takeIf { it.isNotEmpty() },
        )
    }

    companion object {
        /** Create a local (in-memory) game client. */
        fun localClient(game: GameIR): GameClient =
            GameClient(game, LocalRuntime().deploy(game))
    }
}

/**
 * Structured representation of the current game state.
 */
data class GameState(
    val isTerminal: Boolean,
    val roleStates: List<RoleState>,
    val currentMoves: List<MoveOption>,
)

/**
 * Per-role view of available moves.
 */
data class RoleState(
    val role: RoleId,
    val moves: List<MoveOption>,
)

/**
 * A single legal move option.
 */
data class MoveOption(
    val index: Int,
    val actionId: ActionId,
    val role: RoleId,
    val visibility: Visibility,
    val description: String,
    val paramDomains: List<ParamDomain>,
    val prefilledAssignments: Map<VarId, Expr.Const>? = null,
)

/**
 * Domain of a parameter: what values it can take.
 */
data class ParamDomain(
    val name: VarId,
    val type: Type,
    val values: List<Any>?,
)

// ========== Helpers ==========

private fun typeLabel(type: Type): String = when (type) {
    is Type.BoolType -> "bool"
    is Type.IntType -> "int"
    is Type.RangeType -> "{${type.min}..${type.max}}"
}

private fun enumerateDomain(type: Type): List<Any>? = when (type) {
    is Type.BoolType -> listOf(true, false)
    is Type.RangeType -> (type.min..type.max).toList()
    is Type.IntType -> null // unbounded
}

private fun toConst(value: Any, visibility: Visibility): Expr.Const {
    val base = when (value) {
        is Boolean -> Expr.Const.BoolVal(value)
        is Int -> Expr.Const.IntVal(value)
        is Expr.Const -> value
        else -> error("Unsupported value type: ${value::class}")
    }
    return if (visibility == Visibility.COMMIT) Expr.Const.Hidden(base) else base
}

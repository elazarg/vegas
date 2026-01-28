package vegas.runtime

import vegas.RoleId
import vegas.ir.ActionId
import vegas.ir.GameIR
import vegas.ir.asInt
import vegas.semantics.*

/**
 * In-memory game runtime wrapping [GameSemantics].
 * Serves as the reference oracle for correctness testing.
 */
class LocalRuntime : GameRuntime {
    override fun deploy(game: GameIR): GameSession = LocalSession(game)
}

/**
 * A game session backed by the semantic model.
 *
 * Translates between the per-action [GameMove] interface and the
 * frontier-based [Label]/[Configuration] semantic model.
 */
class LocalSession(private val game: GameIR) : GameSession {
    private val semantics = GameSemantics(game)
    private var config = Configuration.initial(game)

    /** Track submitted zero-parameter actions (e.g., joins) in the current frontier. */
    private val submittedZeroParam = mutableSetOf<ActionId>()

    override fun legalMoves(): List<GameMove> =
        MoveTranslator.legalMoves(semantics, config)
            .filter { it.actionId !in submittedZeroParam }

    override fun submitMove(move: GameMove) {
        if (move.assignments.isEmpty()) {
            // Zero-parameter action (e.g., join): the semantic model doesn't
            // require explicit submission. Track it and finalize when all
            // zero-parameter actions in the frontier are submitted.
            submittedZeroParam.add(move.actionId)
            maybeFinalize()
            return
        }

        // Convert the GameMove to a Label.Play
        val frontierSlice = MoveTranslator.moveToFrontierSlice(move)
        val tag = PlayTag.Action(move.actionId)
        val label = Label.Play(move.role, frontierSlice, tag)

        // Apply the move
        config = applyMove(config, label)

        // Auto-finalize frontier if all roles have acted
        maybeFinalize()
    }

    private fun maybeFinalize() {
        if (!semantics.canFinalizeFrontier(config)) return

        // Also wait for all zero-parameter actions to be submitted
        val zeroParamInFrontier = config.enabled().filter { game.dag.params(it).isEmpty() }
        if (!submittedZeroParam.containsAll(zeroParamInFrontier.toSet())) return

        config = applyMove(config, Label.FinalizeFrontier)
        submittedZeroParam.clear()
    }

    override fun isTerminal(): Boolean = config.isTerminal()

    override fun payoffs(): Map<RoleId, Int> {
        require(isTerminal()) { "Cannot compute payoffs: game is not terminal" }

        return game.payoffs.mapValues { (_, expr) ->
            eval({ field -> config.history.get(field) }, expr).asInt()
        }
    }
}

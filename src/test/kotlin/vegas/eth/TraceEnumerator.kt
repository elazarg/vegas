package vegas.eth

import vegas.ir.GameIR
import vegas.runtime.GameMove
import vegas.runtime.MoveTranslator
import vegas.semantics.*
import kotlin.random.Random

/**
 * A complete game trace: the sequence of moves played to reach a terminal state.
 *
 * @property moves The ordered list of moves played
 * @property description Human-readable trace description
 */
data class GameTrace(
    val moves: List<GameMove>,
    val description: String,
)

/**
 * Enumerates complete game traces via DFS over the semantic model.
 *
 * Supports exhaustive enumeration (small games) and random sampling (large games).
 */
object TraceEnumerator {

    /**
     * Exhaustively enumerate all complete game traces.
     * Only feasible for small games (Prisoners, OddsEvens, etc.).
     *
     * @param game The game IR
     * @param maxTraces Maximum number of traces to collect (safety limit)
     * @return All complete traces, up to [maxTraces]
     */
    fun exhaustive(game: GameIR, maxTraces: Int = 1000): List<GameTrace> {
        val semantics = GameSemantics(game)
        val initial = Configuration.initial(game)
        val traces = mutableListOf<GameTrace>()

        fun dfs(config: Configuration, moves: List<GameMove>, depth: Int) {
            if (traces.size >= maxTraces) return

            if (config.isTerminal()) {
                val desc = moves.joinToString(" -> ") {
                    "${it.role}.${it.actionId.second}(${it.assignments.entries.joinToString { (k, v) -> "$k=$v" }})"
                }
                traces.add(GameTrace(moves, desc))
                return
            }

            val labels = semantics.enabledMoves(config)
            val enabled = config.enabled()

            val playLabels = labels.filterIsInstance<Label.Play>()

            if (playLabels.isEmpty() && labels.any { it is Label.FinalizeFrontier }) {
                // Zero-parameter frontier (e.g., joins): auto-finalize and include
                // the zero-param actions as moves in the trace.
                val zeroParamMoves = enabled.filter { game.dag.params(it).isEmpty() }.map { actionId ->
                    GameMove(
                        actionId = actionId,
                        role = game.dag.owner(actionId),
                        visibility = game.dag.meta(actionId).kind,
                        assignments = emptyMap(),
                    )
                }
                val finalized = applyMove(config, Label.FinalizeFrontier)
                dfs(finalized, moves + zeroParamMoves, depth + 1)
            } else {
                for (label in playLabels) {
                    val gameMoves = MoveTranslator.labelToMoves(label, game.dag, enabled)
                    val nextConfig = applyMove(config, label)

                    // Auto-finalize if possible
                    val finalized = if (semantics.canFinalizeFrontier(nextConfig)) {
                        applyMove(nextConfig, Label.FinalizeFrontier)
                    } else {
                        nextConfig
                    }

                    dfs(finalized, moves + gameMoves, depth + 1)
                }
            }
        }

        dfs(initial, emptyList(), 0)
        return traces
    }

    /**
     * Sample random complete game traces using a fixed seed for reproducibility.
     * Useful for large-domain games where exhaustive enumeration is infeasible.
     *
     * At each decision point, picks a random enabled move. Repeats [count] times.
     * Duplicate traces are included (they reflect the probability distribution).
     *
     * @param game The game IR
     * @param count Number of traces to sample
     * @param seed Random seed for reproducibility
     * @return Sampled complete traces
     */
    fun sample(game: GameIR, count: Int, seed: Long = 42): List<GameTrace> {
        val semantics = GameSemantics(game)
        val rng = Random(seed)
        val traces = mutableListOf<GameTrace>()

        repeat(count) {
            var config = Configuration.initial(game)
            val moves = mutableListOf<GameMove>()

            var maxDepth = 200
            while (!config.isTerminal() && maxDepth-- > 0) {
                val labels = semantics.enabledMoves(config)
                val enabled = config.enabled()
                val playLabels = labels.filterIsInstance<Label.Play>()

                if (playLabels.isEmpty() && labels.any { it is Label.FinalizeFrontier }) {
                    // Zero-parameter frontier: auto-finalize
                    val zeroParamMoves = enabled.filter { game.dag.params(it).isEmpty() }.map { actionId ->
                        GameMove(
                            actionId = actionId,
                            role = game.dag.owner(actionId),
                            visibility = game.dag.meta(actionId).kind,
                            assignments = emptyMap(),
                        )
                    }
                    config = applyMove(config, Label.FinalizeFrontier)
                    moves.addAll(zeroParamMoves)
                } else if (playLabels.isNotEmpty()) {
                    val chosen = playLabels[rng.nextInt(playLabels.size)]
                    val gameMoves = MoveTranslator.labelToMoves(chosen, game.dag, enabled)
                    config = applyMove(config, chosen)

                    // Auto-finalize if possible
                    if (semantics.canFinalizeFrontier(config)) {
                        config = applyMove(config, Label.FinalizeFrontier)
                    }
                    moves.addAll(gameMoves)
                } else {
                    break // No moves available
                }
            }

            if (config.isTerminal()) {
                val desc = moves.joinToString(" -> ") {
                    "${it.role}.${it.actionId.second}(${it.assignments.entries.joinToString { (k, v) -> "$k=$v" }})"
                }
                traces.add(GameTrace(moves, desc))
            }
        }

        return traces
    }

}

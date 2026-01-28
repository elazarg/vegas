package vegas.runtime

import vegas.FieldRef
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.semantics.*

/**
 * Translates between the semantic model's [Label.Play] (frontier slices)
 * and the runtime's per-action [GameMove] representation.
 *
 * The semantic model groups all of a role's assignments into a single frontier slice.
 * The runtime model exposes individual action moves for contract interaction.
 */
object MoveTranslator {

    /**
     * Convert a [Label.Play] into a list of [GameMove]s, one per action the role
     * is executing in this frontier.
     *
     * For the semantic model, a role's play contains assignments for all its
     * actions in the current frontier. This splits them back into per-action moves.
     */
    fun labelToMoves(label: Label.Play, dag: ActionDag, enabledActions: Set<ActionId>): List<GameMove> {
        val role = label.role

        // Group the delta's fields by which enabled action they belong to
        val actionsForRole = enabledActions.filter { dag.owner(it) == role }

        return actionsForRole.map { actionId ->
            val meta = dag.meta(actionId)
            val paramNames = meta.spec.params.map { it.name }.toSet()

            // Extract assignments for this action's parameters
            val assignments = label.delta
                .filter { (fieldRef, _) -> fieldRef.owner == role && fieldRef.param in paramNames }
                .map { (fieldRef, value) -> fieldRef.param to value }
                .toMap()

            GameMove(
                actionId = actionId,
                role = role,
                visibility = meta.kind,
                assignments = assignments,
            )
        }
    }

    /**
     * Convert a [GameMove] back into a frontier assignment slice
     * suitable for the semantic model.
     */
    fun moveToFrontierSlice(move: GameMove): FrontierAssignmentSlice {
        return move.assignments.map { (varId, value) ->
            FieldRef(move.role, varId) to value
        }.toMap()
    }

    /**
     * Enumerate all legal [GameMove]s at a given configuration,
     * decomposing frontier plays into per-action moves.
     *
     * The semantic model skips zero-parameter actions (e.g., joins) because
     * they require no player choices. This method also includes those actions
     * so that runtimes can submit explicit transactions for them.
     */
    fun legalMoves(semantics: GameSemantics, config: Configuration): List<GameMove> {
        val labels = semantics.enabledMoves(config)
        val enabled = config.enabled()
        val dag = semantics.ir.dag

        val moves = labels.filterIsInstance<Label.Play>().flatMap { play ->
            labelToMoves(play, dag, enabled)
        }.toMutableList()

        // Include zero-parameter actions (e.g., joins) that the semantic model
        // auto-finalizes but the runtime needs as explicit moves.
        for (actionId in enabled) {
            if (dag.params(actionId).isEmpty() && moves.none { it.actionId == actionId }) {
                moves.add(GameMove(
                    actionId = actionId,
                    role = dag.owner(actionId),
                    visibility = dag.meta(actionId).kind,
                    assignments = emptyMap(),
                ))
            }
        }

        return moves
    }
}

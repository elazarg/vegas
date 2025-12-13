package vegas.ir

import vegas.dag.Dag
import vegas.dag.ExplicitDag

enum class ActionStep { COMMIT, CHOOSE, REVEAL }

data class VisibilityNode(val action: ActionId, val step: ActionStep)

data class VisibilityGraph(
    val dag: Dag<VisibilityNode>
)

object VisibilityGraphBuilder {

    fun build(base: ActionDag): VisibilityGraph {
        fun n(a: ActionId, p: ActionStep) = VisibilityNode(a, p)

        // --- nodes: 3 per action
        val nodes = LinkedHashSet<VisibilityNode>(base.actions.size * 3)
        for (a in base.actions) {
            nodes += n(a, ActionStep.COMMIT)
            nodes += n(a, ActionStep.CHOOSE)
            nodes += n(a, ActionStep.REVEAL)
        }

        // node -> prerequisites
        val prereqs: MutableMap<VisibilityNode, MutableSet<VisibilityNode>> = linkedMapOf()

        fun addEdge(from: VisibilityNode, to: VisibilityNode) {
            prereqs.getOrPut(to) { linkedSetOf() }.add(from)
        }

        // --- informational chain per action
        for (a in base.actions) {
            addEdge(n(a, ActionStep.COMMIT), n(a, ActionStep.CHOOSE))
            addEdge(n(a, ActionStep.CHOOSE), n(a, ActionStep.REVEAL))
        }

        // --- lift causal dependencies
        //
        // For each causal edge y -> x in ActionDag,
        // add exactly one edge into (x, COMMIT) from the appropriate step of y.
        for (x in base.actions) {
            val ownerX = base.owner(x)

            for (y in base.prerequisitesOf(x)) {
                val ownerY = base.owner(y)
                val visY = base.kind(y)

                val srcStep = when {
                    // same owner OR y is public
                    ownerX == ownerY || visY == Visibility.PUBLIC ->
                        ActionStep.CHOOSE

                    // different owners, committed
                    visY == Visibility.COMMIT ->
                        ActionStep.COMMIT

                    // different owners, revealed
                    visY == Visibility.REVEAL ->
                        ActionStep.REVEAL

                    else ->
                        error("Unhandled visibility case for action $y")
                }

                addEdge(n(y, srcStep), n(x, ActionStep.COMMIT))
            }
        }

        val dag: Dag<VisibilityNode> = try {
            ExplicitDag.from(
                nodes = nodes,
                prerequisitesOf = { node -> prereqs[node].orEmpty() },
                checkAcyclic = true
            ) ?: error("VisibilityGraph is cyclic (unexpected)")
        } catch (e: IllegalArgumentException) {
            // ExplicitDag.from throws IllegalArgumentException on cycle
            throw IllegalStateException("VisibilityGraph is cyclic (unexpected)", e)
        }

        return VisibilityGraph(dag)
    }
}

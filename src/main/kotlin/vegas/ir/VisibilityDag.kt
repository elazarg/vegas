package vegas.ir

import vegas.dag.Dag
import vegas.dag.ExplicitDag
import vegas.dag.before

enum class Phase { COMMIT_EVENT, CHOICE, REVEAL_EVENT }

data class PhaseNode(val action: ActionId, val phase: Phase)

class VisibilityGraph private constructor(
    private val inner: Dag<PhaseNode>
) : Dag<PhaseNode> by inner {
    companion object {
        fun build(base: ActionDag): VisibilityGraph {
            val dag: Dag<PhaseNode> = ExplicitDag.fromEdges(
                edges = base.actions.flatMap { a -> chain(a) + deps(base, a) }.toSet(),
                checkAcyclic = true
            ) ?: error("VisibilityGraph is cyclic (unexpected)")

            return VisibilityGraph(dag)
        }

        private fun deps(
            base: ActionDag,
            a: ActionId
        ): List<Pair<PhaseNode, PhaseNode>> = base.prerequisitesOf(a).map { y ->
            val srcPhase =
                when (base.kind(y)) {
                    Visibility.REVEAL -> Phase.REVEAL_EVENT
                    Visibility.PUBLIC -> Phase.CHOICE
                    Visibility.COMMIT ->
                        if (base.owner(a) == base.owner(y))
                            Phase.CHOICE
                        else
                            Phase.COMMIT_EVENT
                }
            PhaseNode(y, srcPhase) before PhaseNode(a, Phase.COMMIT_EVENT)
        }

        private fun chain(a: ActionId): List<Pair<PhaseNode, PhaseNode>> {
            return listOf(
                PhaseNode(a, Phase.COMMIT_EVENT) before PhaseNode(a, Phase.CHOICE),
                PhaseNode(a, Phase.CHOICE) before PhaseNode(a, Phase.REVEAL_EVENT),
            )
        }
    }
}

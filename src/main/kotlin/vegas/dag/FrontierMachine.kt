package vegas.dag

import java.util.Collections.unmodifiableSet

class FrontierMachine<T : Any> private constructor(
    private val dependents: Map<T, Set<T>>,
    private val unresolved: MutableSet<T>,
    private val enabled: MutableSet<T>,
    private val remainingDeps: MutableMap<T, Int>
) {
    fun enabled(): Set<T> = unmodifiableSet(LinkedHashSet(enabled))
    fun isComplete(): Boolean = unresolved.isEmpty()

    fun resolve(node: T) {
        require(node in enabled) { "Node $node is not enabled." }
        unresolved.remove(node); enabled.remove(node)
        dependents[node]?.forEach { d ->
            if (d in unresolved) {
                val c = remainingDeps.getValue(d) - 1
                remainingDeps[d] = c
                if (c == 0) enabled.add(d)
            }
        }
    }
    companion object {
        fun <T : Any> from(dag: Dag<T>): FrontierMachine<T> {
            val depsCount = dag.nodes.associateWith { dag.prerequisitesOf(it).size }.toMutableMap()
            val dependents = dag.dependentsMap()
            val initial = dag.nodes.filter { depsCount[it] == 0 }.toMutableSet()
            return FrontierMachine(dependents, dag.nodes.toMutableSet(), initial, depsCount)
        }
    }

    // diagnostic helpers
    fun unresolved(): Set<T> = unmodifiableSet(LinkedHashSet(unresolved))
    fun remainingDepsOf(n: T): Int = remainingDeps[n] ?: 0
}

package vegas.dag

class FrontierMachine<T : Any> private constructor(
    private val dependents: Map<T, Set<T>>,
    private val unresolved: Set<T>,
    private val enabled: Set<T>,
    private val remainingDeps: Map<T, Int>
) {
    /** Currently enabled nodes. */
    fun enabled(): Set<T> = enabled

    /** All nodes that have not yet been resolved. */
    fun unresolved(): Set<T> = unresolved

    /** Number of unresolved prerequisites of n. */
    fun remainingDepsOf(n: T): Int = remainingDeps[n] ?: 0

    /** All nodes have been resolved. */
    fun isComplete(): Boolean = unresolved.isEmpty()

    /**
     * Resolve one enabled node and return a new FrontierMachine.
     * Does not mutate the current instance.
     */
    fun resolve(node: T): FrontierMachine<T> {
        require(node in enabled) { "Node $node is not enabled." }

        val newUnresolved = unresolved - node
        val newEnabled: MutableSet<T> = (enabled - node).toMutableSet()
        val newRemainingDeps = remainingDeps.toMutableMap()

        dependents[node]?.forEach { d ->
            if (d in newUnresolved) {
                val c = newRemainingDeps.getValue(d) - 1
                newRemainingDeps[d] = c
                if (c == 0) newEnabled.add(d)
            }
        }

        return FrontierMachine(
            dependents = dependents,
            unresolved = newUnresolved,
            enabled = newEnabled,
            remainingDeps = newRemainingDeps
        )
    }

    companion object {
        fun <T : Any> from(dag: Dag<T>): FrontierMachine<T> {
            val depsCount = dag.nodes
                .associateWith { dag.prerequisitesOf(it).size }
                .toMutableMap()

            val dependents = dag.nodes
                .associateWith { dag.dependentsOf(it) }

            val initialEnabled = dag.nodes
                .filter { depsCount[it] == 0 }
                .toSet()

            return FrontierMachine(
                dependents = dependents,
                unresolved = dag.nodes.toSet(),
                enabled = initialEnabled,
                remainingDeps = depsCount
            )
        }
    }
}

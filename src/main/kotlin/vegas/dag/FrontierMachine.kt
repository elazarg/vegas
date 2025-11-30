package vegas.dag

class FrontierMachine<T : Any> private constructor(
    private val dependents: Map<T, Set<T>>,
    private val unresolved: Set<T>,
    private val enabled: Set<T>,
    private val remainingDeps: Map<T, Int>
) {
    /** Currently enabled nodes. */
    fun enabled(): Set<T> = enabled

    /** All nodes have been resolved. */
    fun isComplete(): Boolean = unresolved.isEmpty()

    /**
     * Resolve all enabled node and return a new FrontierMachine.
     * Does not mutate the current instance.
     */
    fun resolveEnabled(): FrontierMachine<T> {
        val newUnresolved = unresolved - enabled
        val newEnabled: MutableSet<T> = mutableSetOf()
        val newRemainingDeps = remainingDeps.toMutableMap()
        for (node in enabled) {
            dependents[node]?.forEach { d ->
                if (d in newUnresolved) {
                    val c = newRemainingDeps.getValue(d) - 1
                    newRemainingDeps[d] = c
                    if (c == 0) newEnabled.add(d)
                }
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

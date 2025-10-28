package vegas.dag

import java.util.Collections.unmodifiableMap
import java.util.Collections.unmodifiableSet

interface Dag<T : Any> {
    val nodes: Set<T>
    fun prerequisitesOf(n: T): Set<T>
    fun dependentsOf(n: T): Set<T>
    fun sliceFrom(terminals: Set<T>): Dag<T>
    fun topo(): List<T>
}

/* ===========================
   Concrete immutable DAG impls
   =========================== */

class ExplicitDag<T : Any> internal constructor(
    override val nodes: Set<T>,
    internal val prereq: Map<T, Set<T>>
) : Dag<T> {

    private val dependents: Map<T, Set<T>> by lazy(LazyThreadSafetyMode.NONE) {
        Algo.buildDependents(nodes, prereq)
    }
    private val topoOrder: List<T> by lazy(LazyThreadSafetyMode.NONE) {
        Algo.topo(nodes, prereq)
    }

    override fun prerequisitesOf(n: T): Set<T> = prereq[n].orEmpty()
    override fun dependentsOf(n: T): Set<T> = dependents[n].orEmpty()
    override fun topo(): List<T> = topoOrder

    override fun sliceFrom(terminals: Set<T>): DagSlice<T> {
        require(terminals.all { it in nodes }) { "sliceFrom: terminal not in DAG nodes" }
        val (keep, p2) = Algo.buildSlice(prereq, terminals)
        return DagSlice(keep, p2)
    }

    companion object {
        fun <T : Any> from(
            nodes: Set<T>,
            prerequisitesOf: (T) -> Set<T>,
            checkAcyclic: Boolean = false
        ): Dag<T> {
            val nSet = LinkedHashSet<T>(nodes.size).apply { addAll(nodes) }
            val pMap = LinkedHashMap<T, Set<T>>(nSet.size).apply {
                for (n in nSet) {
                    val ps = prerequisitesOf(n)
                    require(ps.all { it in nSet }) { "Prereq outside node set for $n" }
                    put(n, unmodifiableSet(LinkedHashSet<T>(ps.size).apply { addAll(ps) }))
                }
            }
            if (checkAcyclic) require(Algo.isAcyclic(nSet, pMap)) { "Cycle detected" }
            return ExplicitDag(unmodifiableSet(nSet), unmodifiableMap(pMap))
        }
    }
}

data class DagSlice<T : Any>(
    override val nodes: Set<T>,
    internal val prereq: Map<T, Set<T>>
) : Dag<T> {

    private val dependents: Map<T, Set<T>> by lazy(LazyThreadSafetyMode.NONE) {
        Algo.buildDependents(nodes, prereq)
    }
    private val topoOrder: List<T> by lazy(LazyThreadSafetyMode.NONE) {
        Algo.topo(nodes, prereq)
    }

    override fun prerequisitesOf(n: T): Set<T> = prereq[n].orEmpty()
    override fun dependentsOf(n: T): Set<T> = dependents[n].orEmpty()
    override fun topo(): List<T> = topoOrder

    override fun sliceFrom(terminals: Set<T>): Dag<T> {
        require(terminals.all { it in nodes }) { "sliceFrom: terminal not in DAG nodes" }
        val (keep, p2) = Algo.buildSlice(prereq, terminals)
        return DagSlice(keep, p2)
    }
}

package vegas.dag

import java.util.Collections.unmodifiableMap
import java.util.Collections.unmodifiableSet

internal object Algo {
    private data class KahnPrep<T: Any>(
        val indeg: LinkedHashMap<T, Int>,
        val dep: LinkedHashMap<T, MutableSet<T>>
    )

    private fun <T: Any> prepKahn(nodes: Set<T>, p: Map<T, Set<T>>): KahnPrep<T> {
        val indeg = LinkedHashMap<T, Int>(nodes.size)
        nodes.forEach { indeg[it] = p[it]?.size ?: 0 }

        val dep = LinkedHashMap<T, MutableSet<T>>(nodes.size)
        nodes.forEach { dep[it] = LinkedHashSet() }
        for ((n, ps) in p) for (q in ps) dep.getValue(q).add(n)

        return KahnPrep(indeg, dep)
    }

    /** Runs Kahn once. Returns a stable topological order or null if a cycle exists. */
    private fun <T: Any> kahnOrder(nodes: Set<T>, p: Map<T, Set<T>>): List<T>? {
        val (indeg, dep) = prepKahn(nodes, p)
        val q = ArrayDeque<T>().apply { nodes.filterTo(this) { indeg.getValue(it) == 0 } }
        val order = ArrayList<T>(nodes.size)

        while (q.isNotEmpty()) {
            val u = q.removeFirst()
            order.add(u)
            for (v in dep.getValue(u)) {
                val d = indeg.getValue(v) - 1
                indeg[v] = d
                if (d == 0) q.addLast(v)
            }
        }
        return if (order.size == nodes.size) order else null
    }

    /** Topological order. */
    fun <T: Any> topo(nodes: Set<T>, prereq: Map<T, Set<T>>): List<T> =
        kahnOrder(nodes, prereq) ?: error("Graph contains a cycle; no topo order.")

    /** True iff acyclic. */
    fun <T: Any> isAcyclic(nodes: Set<T>, prereq: Map<T, Set<T>>): Boolean =
        kahnOrder(nodes, prereq) != null

    fun <T : Any> findCycle(nodes: Set<T>, prereq: Map<T, Set<T>>): List<T> {
        var bestCycle: List<T>? = null
        var bestLen: Int = Int.MAX_VALUE

        for (start in nodes) {
            // BFS over the reversed graph using prereq as adjacency:
            // edge u -> v (original) becomes v -> u here.
            val q = ArrayDeque<T>()
            val dist = mutableMapOf<T, Int>()
            val parent = mutableMapOf<T, T?>()

            q.add(start)
            dist[start] = 0
            parent[start] = null

            while (q.isNotEmpty()) {
                val u = q.removeFirst()
                val du = dist.getValue(u)

                // Small pruning: no point exploring paths already as long
                // as the best cycle we've found.
                if (du + 1 >= bestLen) continue

                for (p in prereq[u].orEmpty()) {
                    // p is a predecessor of u in the original graph,
                    // i.e., p -> u edge. Here we traverse u -> p.

                    if (!dist.containsKey(p)) {
                        dist[p] = du + 1
                        parent[p] = u
                        q.add(p)
                    }

                    // Found a cycle back to start (in reversed graph),
                    // so in original graph we also have a cycle.
                    if (p == start) {
                        val len = du + 1
                        if (len < bestLen) {
                            bestLen = len
                            // reconstruct path start -> ... -> u, then edge u -> start
                            val path = mutableListOf<T>()
                            var cur: T? = u
                            while (cur != null) {
                                path.add(cur)
                                cur = parent[cur]
                            }
                            path.reverse()
                            val cycle = path + start
                            bestCycle = cycle
                        }
                    }
                }
            }
        }

        return bestCycle ?: emptyList()
    }

    /** Build dependents map once, with stable iteration, read-only views. */
    fun <T: Any> buildDependents(nodes: Set<T>, prereq: Map<T, Set<T>>): Map<T, Set<T>> {
        val m = LinkedHashMap<T, MutableSet<T>>(nodes.size * 2)
        nodes.forEach { m[it] = LinkedHashSet() }
        for ((n, ps) in prereq) for (p in ps) m.getValue(p).add(n)
        val out = LinkedHashMap<T, Set<T>>(m.size)
        for ((k, v) in m) out[k] = unmodifiableSet(LinkedHashSet(v))
        return unmodifiableMap(out)
    }

    /** Compute backward-closure slice. */
    fun <T: Any> buildSlice(
        prereq: Map<T, Set<T>>,
        terminals: Set<T>
    ): Pair<Set<T>, Map<T, Set<T>>> {
        val keep = LinkedHashSet<T>()
        val st = ArrayDeque<T>().apply { terminals.forEach { addLast(it) } }
        while (st.isNotEmpty()) {
            val u = st.removeLast()
            if (!keep.add(u)) continue
            prereq[u].orEmpty().forEach { st.addLast(it) }
        }
        val p2 = LinkedHashMap<T, Set<T>>(keep.size)
        for (n in keep) {
            val ps = prereq[n].orEmpty()
            val inter = LinkedHashSet<T>(ps.size).apply { ps.forEach { if (it in keep) add(it) } }
            p2[n] = unmodifiableSet(inter)
        }
        return unmodifiableSet(keep) to unmodifiableMap(p2)
    }
}

interface Reachability<T: Any> {
    fun ancestorsOf(v: T): Set<T>
    fun descendantsOf(v: T): Set<T>
    fun comparable(u: T, v: T): Boolean  // u≤v or v≤u
    fun reaches(u: T, v: T): Boolean     // u->* v
}

fun <T : Any> computeReachability(slice: DagSlice<T>): Reachability<T> {
    val topo = Algo.topo(slice.nodes, slice.prereq)
    val index = LinkedHashMap<T, Int>(topo.size).apply { topo.forEachIndexed { i, v -> put(v, i) } }
    val n = topo.size

    val anc = Array(n) { java.util.BitSet(n) }
    val depMap = Algo.buildDependents(slice.nodes, slice.prereq)

    // ancestors: forward DP
    for (v in topo) {
        val vi = index.getValue(v)
        for (p in slice.prereq[v].orEmpty()) {
            val pi = index.getValue(p)
            anc[vi].or(anc[pi])
            anc[vi].set(pi)
        }
    }

    // descendants: reverse DP
    val desc = Array(n) { java.util.BitSet(n) }
    for (v in topo.asReversed()) {
        val vi = index.getValue(v)
        for (d in depMap[v].orEmpty()) {
            val di = index.getValue(d)
            desc[vi].or(desc[di])
            desc[vi].set(di)
        }
    }

    fun bitsetToSet(bs: java.util.BitSet): Set<T> {
        val out = LinkedHashSet<T>()
        var i = bs.nextSetBit(0)
        while (i >= 0) { out.add(topo[i]); i = bs.nextSetBit(i + 1) }
        return unmodifiableSet(out)
    }

    return object : Reachability<T> {
        override fun ancestorsOf(v: T): Set<T> = bitsetToSet(anc[index.getValue(v)])
        override fun descendantsOf(v: T): Set<T> = bitsetToSet(desc[index.getValue(v)])
        override fun comparable(u: T, v: T): Boolean {
            val ui = index.getValue(u); val vi = index.getValue(v)
            return anc[vi].get(ui) || anc[ui].get(vi)
        }
        override fun reaches(u: T, v: T): Boolean {
            val ui = index.getValue(u); val vi = index.getValue(v)
            return desc[ui].get(vi)
        }
    }
}

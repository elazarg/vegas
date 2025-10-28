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

    /** True iff acyclic (i.e., Kahn succeeds). */
    fun <T: Any> isAcyclic(nodes: Set<T>, p: Map<T, Set<T>>): Boolean =
        kahnOrder(nodes, p) != null

    /** Stable topological order; throws if cyclic. */
    fun <T: Any> topo(nodes: Set<T>, p: Map<T, Set<T>>): List<T> =
        kahnOrder(nodes, p) ?: error("Graph contains a cycle; no topo order.")


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

fun <T: Any> Dag<T>.dependentsMap(): Map<T, Set<T>> =
    nodes.associateWith { dependentsOf(it) }

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

data class PathCoverResult<T:Any>(val paths: List<List<T>>)

private const val NIL = -1

/** DAG minimum vertex-disjoint path cover via bipartite reduction + Hopcroft–Karp. */
fun <T:Any> minPathCover(slice: DagSlice<T>): PathCoverResult<T> {
    val topo = slice.topo()
    val index = topo.withIndex().associate { it.value to it.index }
    val n = topo.size

    // Build adjacency for the bipartite graph (L->R edge for each DAG edge u->v)
    val adj = Array(n) { IntArray(0) }
    val temp = Array(n) { ArrayList<Int>() }
    for ((v, ps) in slice.prereq) {
        val vi = index.getValue(v)
        for (p in ps) {
            val pi = index.getValue(p)
            // edge p -> v in DAG => edge (p in L) -> (v in R) in bipartite
            temp[pi].add(vi)
        }
    }
    for (i in 0 until n) adj[i] = temp[i].toIntArray()

    // Hopcroft–Karp
    val pairU = IntArray(n) { NIL } // left -> right
    val pairV = IntArray(n) { NIL } // right -> left
    val dist  = IntArray(n) { 0 }

    fun bfs(): Boolean {
        val q = ArrayDeque<Int>()
        for (u in 0 until n) {
            if (pairU[u] == NIL) { dist[u] = 0; q.addLast(u) } else dist[u] = Int.MAX_VALUE
        }
        var found = false
        while (q.isNotEmpty()) {
            val u = q.removeFirst()
            for (v in adj[u]) {
                val pu = pairV[v]
                if (pu == NIL) {
                    found = true
                } else if (dist[pu] == Int.MAX_VALUE) {
                    dist[pu] = dist[u] + 1
                    q.addLast(pu)
                }
            }
        }
        return found
    }

    fun dfs(u: Int): Boolean {
        for (v in adj[u]) {
            val pu = pairV[v]
            if (pu == NIL || (dist[pu] == dist[u] + 1 && dfs(pu))) {
                pairU[u] = v
                pairV[v] = u
                return true
            }
        }
        dist[u] = Int.MAX_VALUE
        return false
    }

    while (bfs()) {
        for (u in 0 until n) if (pairU[u] == NIL) dfs(u)
    }

    // Reconstruct paths: start at vertices with no matched predecessor on the left
    val hasPred = BooleanArray(n)
    for (v in 0 until n) {
        val u = pairV[v]
        if (u != NIL) hasPred[v] = true
    }

    val paths = ArrayList<List<T>>()
    val used = BooleanArray(n)
    for (u in 0 until n) {
        if (!hasPred[u]) {
            // start of a path
            val path = ArrayList<T>()
            var x = u
            while (x != NIL && !used[x]) {
                path.add(topo[x]); used[x] = true
                val y = pairU[x]
                x = if (y == NIL) NIL else y
            }
            if (path.isNotEmpty()) paths.add(path)
        }
    }
    // Any unmatched, unused vertices are singleton paths
    for (i in 0 until n) if (!used[i]) paths.add(listOf(topo[i]))

    return PathCoverResult(paths)
}

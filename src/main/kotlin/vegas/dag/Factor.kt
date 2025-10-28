package vegas.dag

import java.util.Collections.unmodifiableSet


/* ===========================
   Ordinal-sum-of-antichains
   =========================== */

data class OrdinalSumResult<T : Any>(
    val isExact: Boolean,
    val stages: List<Set<T>>,                    // when exact
    val witnessInternalEdges: List<Pair<T, T>>,   // if !isExact
    val witnessCrossIncomparables: List<Pair<T, T>> // if !isExact
)

/**
 * Factor a DAG exactly as an ordinal sum of antichains A1 + A2 + ... + Ak, if possible.
 * Criterion:
 *  - Group nodes by identical Anc(v); sort groups by inclusion; inside each group must be edgeless;
 *  - All cross pairs across earlier->later groups must be comparable forward.
 */
fun <T : Any> factorOrdinalSum(slice: DagSlice<T>, rc: Reachability<T>): OrdinalSumResult<T> {
    val topo = slice.topo()
    val index = topo.withIndex().associate { it.value to it.index }
    val n = topo.size

    // Build BitSet keys of ancestors for grouping
    val anc = Array(n) { java.util.BitSet(n) }
    topo.forEachIndexed { vi, v ->
        for (p in slice.prereq[v].orEmpty()) {
            val pi = index.getValue(p)
            anc[vi].or(anc[pi])
            anc[vi].set(pi)
        }
    }

    // Group by identical anc BitSet (BitSet has value semantics for equals/hashCode)
    val groups = LinkedHashMap<java.util.BitSet, MutableList<T>>()
    topo.forEachIndexed { i, v ->
        val b = anc[i].clone() as java.util.BitSet
        groups.computeIfAbsent(b) { mutableListOf() }.add(v)
    }

    // Sort groups by inclusion (fallback tie-breaker: size, then topo order of first)
    data class G<T>(val key: java.util.BitSet, val members: List<T>, val minIndex: Int)

    val gs = groups.entries.map { e ->
        val minI = e.value.minOf { index.getValue(it) }
        G(e.key, e.value.toList(), minI)
    }.sortedWith { a, b ->
        val ca = a.key.cardinality()
        val cb = b.key.cardinality()
        if (ca != cb) ca - cb
        else a.minIndex - b.minIndex
    }

    // Verify inclusion chain and collect stages
    val stages = ArrayList<Set<T>>(gs.size)
    for (i in gs.indices) {
        if (i > 0) {
            val prev = gs[i - 1].key
            val cur = gs[i].key
            val prevMinusCur = prev.clone() as java.util.BitSet; prevMinusCur.andNot(cur)
            if (!prevMinusCur.isEmpty) {
                // Not a chain by inclusion. Find an actual cross-boundary pair (a in prev, b in cur)
                // where a !-> b (i.e., not rc.reaches(a,b)).
                var wa: T? = null
                var wb: T? = null
                outer@ for (a in gs[i - 1].members) for (b in gs[i].members) {
                    if (!rc.reaches(a, b)) {
                        wa = a; wb = b; break@outer
                    }
                }
                val witness = if (wa != null) listOf(wa to wb!!) else emptyList()
                return OrdinalSumResult(
                    isExact = false,
                    stages = emptyList(),
                    witnessInternalEdges = emptyList(),
                    witnessCrossIncomparables = witness
                )
            }
        }
        stages.add(unmodifiableSet(LinkedHashSet(gs[i].members)))
    }

    // Check each stage is an antichain (no edges inside)
    val internalViol = mutableListOf<Pair<T, T>>()
    for (st in stages) {
        val lst = st.toList()
        for (i in lst.indices) for (j in i + 1 until lst.size) {
            val a = lst[i]
            val b = lst[j]
            if (rc.reaches(a, b) || rc.reaches(b, a)) {
                internalViol.add(a to b)
                if (internalViol.size >= 8) break
            }
        }
        if (internalViol.isNotEmpty()) break
    }
    if (internalViol.isNotEmpty()) {
        return OrdinalSumResult(false, emptyList(), internalViol, emptyList())
    }

    // Check full comparability across adjacent stages in the forward direction
    val crossInc = mutableListOf<Pair<T, T>>()
    for (i in 0 until stages.size - 1) {
        loop@ for (a in stages[i]) for (b in stages[i + 1]) {
            if (!rc.reaches(a, b)) {
                crossInc.add(a to b)
                if (crossInc.size >= 8) break@loop
            }
        }
        if (crossInc.isNotEmpty()) break
    }
    if (crossInc.isNotEmpty()) {
        return OrdinalSumResult(false, emptyList(), emptyList(), crossInc)
    }

    return OrdinalSumResult(true, stages, emptyList(), emptyList())
}

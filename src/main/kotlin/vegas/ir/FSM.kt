package vegas.ir

/**
 * Immutable specification of a finite **dependency DAG** over nodes of type [T].
 *
 * ### Purpose
 * Represents the static structure of the information dependence: for each node `n`, the set of its
 * prerequisites (immediate dependencies) `prerequisitesOf(n)`.
 *
 * ### Definitions
 * - **Prerequisite edge**: `p → n` means `n` requires `p` to be resolved before `n` can resolve.
 * - **Dependents map**: derived relation `n ← p` used to update nodes when `p` completes.
 * - **Backward closure** from a terminal set `T`: the induced subgraph on all nodes that can
 *   reach some `t ∈ T` by following prerequisite edges backward.
 *
 * ### Operations
 * - [prerequisitesOf]: total over [nodes]; returns the (possibly empty) prerequisite set.
 * - [dependentsMap]: computed on demand; returns for each node the set of nodes that directly
 *   depend on it (may be empty).
 * - [viewFrom]: computes the backward closure from a given set of terminals and returns an
 *   *independent* DAG spec restricted to that induced subgraph.
 *
 * ### Invariants
 * - All prerequisites are members of [nodes].
 * - Optionally, acyclicity is checked at construction time (`checkAcyclic=true`).
 *
 * ### Why this layer exists
 * Analyses, exporters (e.g., PNML/Petri nets), and proofs should consume an **immutable graph
 * specification**. The mutable, stateful frontier/queue belongs to a separate machine layer.
 *
 * ### Complexity notes
 * - [dependentsMap] is O(|E|) to construct (E = set of edges).
 * - [viewFrom] is O(|V| + |E|) over the explored subgraph.
 */
class TaskDAG<T : Any> private constructor(
    val nodes: Set<T>,
    private val prereqs: Map<T, Set<T>>
) {
    /** Prerequisites of a node (empty set if none). Total on [nodes]. */
    fun prerequisitesOf(n: T): Set<T> = prereqs[n] ?: emptySet()

    /** Derived: dependents map (node -> who directly depends on it). */
    fun dependentsMap(): Map<T, Set<T>> {
        val out = mutableMapOf<T, MutableSet<T>>()
        for ((n, ps) in prereqs) for (p in ps) out.getOrPut(p) { mutableSetOf() }.add(n)
        // Ensure every node appears (even if no dependents)
        for (n in nodes) out.putIfAbsent(n, mutableSetOf())
        return out.mapValues { it.value.toSet() }
    }

    /** Backward closure from a terminal set: induced subgraph of nodes that can reach a terminal. */
    fun viewFrom(terminals: Set<T>): TaskDAG<T> {
        val keep = mutableSetOf<T>()
        val stack = ArrayDeque<T>().apply { addAll(terminals) }
        while (stack.isNotEmpty()) {
            val n = stack.removeLast()
            if (!keep.add(n)) continue
            for (p in prereqs[n].orEmpty()) stack.addLast(p)
        }
        val p2 = keep.associateWith { n -> prereqs[n].orEmpty().intersect(keep) }
        return TaskDAG(keep, p2)
    }

    companion object {
        /**
         * Build a DAG spec from nodes and a prerequisite function.
         * Preconditions (checked defensively in debug builds): all prereqs ∈ nodes; graph is acyclic.
         */
        fun <T : Any> from(
            nodes: Set<T>,
            prerequisitesOf: (T) -> Set<T>,
            checkAcyclic: Boolean = false
        ): TaskDAG<T> {
            val p = nodes.associateWith { n ->
                val ps = prerequisitesOf(n)
                require(ps.all { it in nodes }) { "Prereq outside node set: $n <- $ps" }
                ps
            }
            if (checkAcyclic) require(isAcyclic(nodes, p)) { "Cycle detected in TaskDAG" }
            return TaskDAG(nodes, p)
        }

        private enum class VisitState { UNVISITED, IN_PROGRESS, DONE }

        private fun <T : Any> isAcyclic(
            nodes: Set<T>,
            prereq: Map<T, Set<T>>
        ): Boolean {
            val state = nodes.associateWith { VisitState.UNVISITED }.toMutableMap()

            fun dfs(n: T): Boolean {
                state[n] = VisitState.IN_PROGRESS
                for (p in prereq[n].orEmpty()) {
                    when (state[p]!!) {
                        VisitState.IN_PROGRESS -> return false       // back edge ⇒ cycle
                        VisitState.UNVISITED -> if (!dfs(p)) return false
                        VisitState.DONE -> {}
                    }
                }
                state[n] = VisitState.DONE
                return true
            }

            for (n in nodes) if (state[n] == VisitState.UNVISITED && !dfs(n)) return false
            return true
        }
    }
}

/**
 * Mutable **frontier machine** that runs Kahn’s algorithm over a chosen DAG slice.
 *
 * ### Purpose
 * Maintains the dynamic state required for topological advancement over an **acyclic** graph:
 * - the set of **unresolved** nodes,
 * - the **enabled** frontier (unresolved nodes whose prerequisites are all resolved),
 * - per-node **remaining dependency counts**,
 * - and the **dependents** relation to update counts after a resolution.
 *
 * ### Semantics
 * - A node is **enabled** iff all of its prerequisites are resolved.
 * - [resolve(node)] is permitted **only** for enabled nodes and atomically:
 *   1. removes `node` from unresolved and from the enabled frontier,
 *   2. decrements the remaining-dependency count of its dependents,
 *   3. adds any dependent whose count reaches zero to the enabled frontier.
 *
 * ### Progress & Deadlocks (structural)
 * - **Complete**: no unresolved nodes remain.
 * - **Graph deadlock**: unresolved nodes exist and the enabled frontier is empty.
 *   This reflects a **structural** impossibility to proceed within the explored slice
 *   (e.g., a cycle or missing prerequisites in the slice).
 *
 * ### Division of concerns
 * - The machine **does not encode preferences** or tie-breaking. It only says what *can* run.
 * - Policies (e.g., last-mover advantage) belong in a separate scheduler layer.
 *
 * ### Preconditions
 * - The input slice must be **acyclic**. If a cycle is reachable, the machine’s
 *   enabled frontier is empty at initialization and remains empty (graph deadlock).
 *
 * ### Complexity
 * - Initialization: O(|V| + |E|) over the slice.
 * - Each [resolve] updates adjacent edges in O(out-degree(node)).
 */
class TaskResolutionMachine<T : Any> private constructor(
    private val dependents: Map<T, Set<T>>,
    private val unresolved: MutableSet<T>,
    private val enabled: MutableSet<T>,
    private val remainingDeps: MutableMap<T, Int>
) {
    fun enabled(): Set<T> = enabled.toSet()

    fun isComplete(): Boolean = unresolved.isEmpty()

    fun resolve(node: T) {
        require(node in enabled) { "Node $node is not enabled." }
        unresolved.remove(node)
        enabled.remove(node)
        dependents[node]?.forEach { d ->
            if (d in unresolved) {
                val c = remainingDeps.getValue(d) - 1
                remainingDeps[d] = c
                if (c == 0) enabled.add(d)
            }
        }
    }

    companion object {
        /** Initialize machine over a DAG slice (usually `dag.viewFrom(terminals)`). */
        fun <T : Any> fromSlice(slice: TaskDAG<T>): TaskResolutionMachine<T> {
            val depsCount = slice.nodes.associateWith { n -> slice.prerequisitesOf(n).size }.toMutableMap()
            val dependents = slice.dependentsMap()
            val initialEnabled = slice.nodes.filter { depsCount[it] == 0 }.toMutableSet()
            return TaskResolutionMachine(
                dependents = dependents,
                unresolved = slice.nodes.toMutableSet(),
                enabled = initialEnabled,
                remainingDeps = depsCount
            )
        }
    }
}

/**
 * Scheduler layer for **Last-Mover Advantage (LMA)** over a frontier machine.
 *
 * ### Assumptions (LMA)
 * - **Waiting is free**: there is no penalty or deadline for deferring a move.
 * - **Strict last-move preference**: whenever at least two owners (colors) have enabled tasks,
 *   each prefers someone else to move first.
 * - These are **policy** assumptions; they do not alter the dependency structure.
 *
 * ### Two distinct deadlocks
 * - **Graph deadlock (structural)**: unresolved work exists and the enabled frontier is empty.
 *   Detected by [isGraphDeadlocked]. This is independent of any policy.
 * - **Strategic deadlock (preference)** under LMA: enabled tasks exist but **at least two distinct
 *   owners** are present on the frontier. Then, per LMA, each present owner prefers to wait,
 *   so no one moves. Detected by [isStrategicallyDeadlocked].
 *
 * Formally, let `E = machine.enabled()` and `K = { colorOf(t) | t ∈ E }`. Under LMA:
 *
 *     strategic deadlock  ⇔  |K| ≥ 2
 *
 * This is a property of the **current frontier** only; owners with no enabled tasks are irrelevant
 * to the immediate stalemate.
 *
 * ### Scope
 * The scheduler does **not** resolve ties or choose which task to run. It only classifies the
 * current state. Any tie-breaking, ordering, or fairness belongs to a higher policy.
 */
class LmaScheduler<T : Any, C : Any>(
    private val machine: TaskResolutionMachine<T>,
    private val colorOf: (T) -> C
) {
    /** Structural (Kahn) deadlock: unresolved work exists but the frontier is empty. */
    fun isGraphDeadlocked(): Boolean =
        !machine.isComplete() && machine.enabled().isEmpty()

    /**
     * Strategic deadlock under LMA: enabled tasks exist and at least two distinct colors are present.
     * With LMA, each present color prefers another present color to move first; progress stalls by preference.
     */
    fun isStrategicallyDeadlocked(): Boolean {
        val e = machine.enabled()
        if (e.isEmpty()) return false
        val k = e.asSequence().map(colorOf).toSet().size
        return k >= 2
    }

    /** Colors currently present on the enabled frontier (owners who can act now). */
    fun frontierColors(): Set<C> =
        machine.enabled().asSequence().map(colorOf).toSet()

    /** Current enabled frontier. */
    fun enabled(): Set<T> = machine.enabled()

    /** Advance by resolving a chosen enabled node. */
    fun advance(node: T) = machine.resolve(node)
}

/**
 * Export a dependency DAG as a **Place/Transition Petri net** in **PNML** (PT-net grammar).
 *
 * ### Structural mapping
 * - For each task `x` (node), create a **transition** `T_x`.
 * - For each task `x`, create a **place** `P_x_done` that carries a token iff `x` is resolved.
 * - For each prerequisite edge `p → x`:
 *     - add **input** arc `P_p_done → T_x` with weight 1, and
 *     - add **output** arc `T_x → P_p_done` with weight 1.
 *   This self-loop encodes a **read-arc** in plain PT nets: the prerequisite token is **required**
 *   to enable `T_x` and is **preserved** by firing, matching "once done, always available."
 * - Add **completion** arc `T_x → P_x_done` (weight 1).
 * - Initial marking: zero tokens on all `P_*_done` (no task is pre-completed).
 *
 * ### Semantics correspondence
 * - In any marking, a transition `T_x` is **enabled** iff all its prerequisites’ places carry tokens.
 *   This equals the machine’s `enabled()` predicate over the same DAG slice.
 * - Firing `T_x` produces one token in `P_x_done` and preserves tokens in prerequisite places.
 *
 * ### Analysis compatibility
 * - This encoding works with standard PT-net model checkers (PNML 2009 grammar). Tools that
 *   support true **read-arcs** will treat the self-loop pattern equivalently.
 * - Under interleaving semantics, concurrent enabled transitions that share a prerequisite
 *   become a structural conflict; this is consistent with sequential Kahn advancement.
 *
 * ### Policy separation
 * - **Do not** encode Last-Mover Advantage inside the net. LMA is a **controller/policy**:
 *
 *       strategicDeadlock_LMA(marking)  ⇔  number of distinct owners among enabled transitions ≥ 2
 *
 *   Keep policy outside the structural net to avoid conflating feasibility (tokens) with choice.
 *
 */
object PetriNetPnml {
    private fun xmlEscape(s: String): String = buildString(s.length) {
        for (ch in s) append(
            when (ch) {
                '&' -> "&amp;"; '<' -> "&lt;"; '>' -> "&gt;"; '\"' -> "&quot;"; '\'' -> "&apos;"; else -> "$ch"
            }
        )
    }

    /*
     * - IDs must be unique and XML-safe. Provide a stable [idOf] mapping. Places are named
     *   `"p_${id}_done"`, transitions `"t_${id}"`. [nameOf] is used for human-readable labels.
     */
    fun <T : Any> export(
        dag: TaskDAG<T>,
        idOf: (T) -> String,
        nameOf: (T) -> String = { it.toString() },
        netId: String = "vegas_dag"
    ): String {
        fun pId(n: T) = "p_${idOf(n)}_done"
        fun tId(n: T) = "t_${idOf(n)}"

        val sb = StringBuilder(1 shl 14)
        sb.appendLine("""<?xml version="1.0" encoding="UTF-8"?>""")
        sb.appendLine("""<pnml xmlns="https://www.pnml.org/version-2009/grammar/pnml">""")
        sb.appendLine("""  <net id="${xmlEscape(netId)}" type="https://www.pnml.org/version-2009/grammar/ptnet">""")
        sb.appendLine("""    <page id="page0">""")

        // Places (one per node: "done" marker)
        for (n in dag.nodes) {
            val pid = xmlEscape(pId(n))
            val label = xmlEscape("${nameOf(n)}:done")
            sb.appendLine("""      <place id="$pid"><name><text>$label</text></name><initialMarking><text>0</text></initialMarking></place>""")
        }

        // Transitions (one per node)
        for (n in dag.nodes) {
            val tid = xmlEscape(tId(n))
            val label = xmlEscape(nameOf(n))
            sb.appendLine("""      <transition id="$tid"><name><text>$label</text></name></transition>""")
        }

        // Arcs: completion + read-arc self-loops for each prerequisite
        for (n in dag.nodes) {
            val tid = xmlEscape(tId(n))
            val pidDone = xmlEscape(pId(n))
            sb.appendLine("""      <arc id="a_${tid}_to_${pidDone}" source="$tid" target="$pidDone"><inscription><text>1</text></inscription></arc>""")
            for (p in dag.prerequisitesOf(n)) {
                val pid = xmlEscape(pId(p))
                sb.appendLine("""      <arc id="a_${pid}_to_${tid}" source="$pid" target="$tid"><inscription><text>1</text></inscription></arc>""")
                sb.appendLine("""      <arc id="a_${tid}_to_${pid}" source="$tid" target="$pid"><inscription><text>1</text></inscription></arc>""")
            }
        }

        sb.appendLine("""    </page>""")
        sb.appendLine("""  </net>""")
        sb.appendLine("""</pnml>""")
        return sb.toString()
    }
}

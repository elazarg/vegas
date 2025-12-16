package vegas.backend.gallina

import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.GameIR
import vegas.ir.Type
import java.util.ArrayDeque
import java.util.BitSet

/**
 * FUTURE (v1+): Remove explicit ESM enumeration.
 *
 * Right now we enumerate all reachable down-closed sets (ideals) of the action DAG and emit:
 *   Stage := S0 | S1 | ...
 *   State : Stage -> Type := st0 ... | st1 ... | ...
 *
 * This is convenient for v0, but it bakes in an explicit state-space that is not conceptually
 * necessary: the semantics is causality-based.
 *
 * Planned direction:
 *   - Represent configurations generically as a dependent record:
 *       Record Config := { done : DoneSet; closed : DownClosed done; witnesses : ... }.
 *   - Provide a single generic step lemma/function parameterized by an action whose prerequisites
 *     are in `done`, rather than emitting one function per (stage, action) pair.
 *
 * This aligns better with the Kotlin semantics (`FrontierMachine` + `History`) and makes the
 * “same semantics across backends” story cleaner: both sides become “DAG + configuration + step”.
 */

/**
 * Gallina/Coq typestate backend (v0).
 *
 * Goal:
 *  - Encode causal dependencies "hard by construction" using indexed witness types.
 *  - Generate a typed explicit state machine over down-closed sets of completed actions.
 *  - No quits yet, but generator is structured so that dep types can later become UnlessQuit.
 *  - Crypto/signatures/guards are abstract evidence types.
 *
 * Naming scheme is intentionally simple:
 *  - Payload:  P_Action<i>
 *  - Witness:  W_Action<i>
 *  - Guard witness: GuardW_Action<i>
 *  - Stages:  S<i>
 *  - States:  st<i>
 */
fun genGallinaTypestate(game: GameIR): String {
    val dag = game.dag
    val topo: List<ActionId> = dag.topo()
    val idxOf: Map<ActionId, Int> = topo.withIndex().associate { it.value to it.index }

    // NOTE: Some IR pipelines may not preserve RoleId object identity consistently
    // across GameIR.roles and ActionDag.owner(action). To avoid brittle map lookups,
    // we key role constructors by role *name*.
    val roleNames: List<String> = buildSet {
        game.roles.forEach { add(it.name) }
        dag.actions.forEach { a -> add(dag.owner(a).name) }
    }.toList().sorted()

    val roleCtor: Map<RoleId, String> =
        roleNames.zip(makeUnique(roleNames.map { coqCtor(it) })).toMap().mapKeys { RoleId(it.key) }

    // Collect unique SetTypes (finite enums) to generate inductives.
    val setTypes: Map<Type.SetType, String> = collectSetTypes(dag).entries
        .sortedBy { it.key.values.sorted().joinToString(",") }
        .mapIndexed { i, (t, _) -> t to "T_Set$i" }
        .toMap()

    // Direct dependencies per action, expressed as indices in topo order.
    val depsIdx: List<List<Int>> = topo.map { id ->
        dag.prerequisitesOf(id)
            .map { p -> idxOf.getValue(p) }
            .sorted()
    }

    // Transitive prerequisites ("full prefix") per action.
    // Ancestors are sorted in increasing topo index.
    val ancestorsIdx: List<List<Int>> = computeAncestors(topo.size, depsIdx)

    // Enumerate all reachable down-closed sets (ideals) of the DAG.
    val stages: List<DoneSet> = enumerateDownClosedSets(topo.size, depsIdx)

    // A stable stage id for each done-set.
    val stageIdOf: Map<DoneSet, Int> = stages.withIndex().associate { it.value to it.index }

    // Precompute the witness binders expected by each stage, in topo order.
    val bindersForStage: List<List<Int>> = stages.map { ds ->
        (0 until topo.size).filter { ds.contains(it) }
    }

    fun stageName(k: Int) = "S$k"
    fun stateCtor(k: Int) = "st$k"
    fun payloadName(i: Int) = "P_Action$i"
    fun witnessName(i: Int) = "W_Action$i"
    fun guardWName(i: Int) = "GuardW_Action$i"

    fun coqType(t: Type): String = when (t) {
        Type.IntType -> "Z"
        Type.BoolType -> "bool"
        is Type.SetType -> setTypes.getValue(t)
    }
    fun witSigField(i: Int) = "W_Action${i}_sig"
    fun witGuardField(i: Int) = "W_Action${i}_guard_ok"

    fun payloadField(i: Int, v: VarId): String = coqIdent("a${i}_${v.name}", upperFirst = false)

    fun payloadDecl(i: Int, actionId: ActionId): String {
        val params = dag.params(actionId)
        if (params.isEmpty()) {
            return "Definition ${payloadName(i)} : Type := unit."
        }
        val fields = params.joinToString(";\n") { p ->
            "  ${payloadField(i, p.name)} : ${coqType(p.type)}"
        }
        return buildString {
            appendLine("Record ${payloadName(i)} : Type := {")
            appendLine(fields)
            appendLine("}.")
        }.trimEnd()
    }

    fun witnessType(i: Int): String {
        val anc = ancestorsIdx[i]
        return if (anc.isEmpty()) witnessName(i)
        else "@${witnessName(i)} ${anc.joinToString(" ") { a -> "w$a" }}"
    }

    fun depArgType(depIdx: Int): String = witnessType(depIdx)
    // later: return "UnlessQuit ${roleCtor(depOwner)} (${witnessType(depIdx)})" when needed

    fun guardWType(i: Int, owner: RoleId): String {
        val anc = ancestorsIdx[i]
        val ancBinders = anc.joinToString(" ") { a -> "(w$a : ${witnessType(a)})" }
        val sigBinder = "(sig : Signed ${roleCtor[owner]} ${payloadName(i)})"
        val all = listOf(ancBinders, sigBinder).filter { it.isNotBlank() }.joinToString(" ")
        return "forall $all, Type"
    }

    fun stateCtorDecl(stageIdx: Int, done: List<Int>): String {
        val ctor = stateCtor(stageIdx)
        val st = stageName(stageIdx)
        if (done.isEmpty()) return "| $ctor : State $st"

        // Quantify witnesses in topo order; each witness type is indexed by its deps.
        val qs = done.joinToString(" ") { i ->
            "(w$i : ${witnessType(i)})"
        }
        return "| $ctor : forall $qs, State $st"
    }

    fun stepFunName(actionIdx: Int, fromStage: Int): String = "step_Action${actionIdx}_from_S$fromStage"

    /**
     * Generate a step function from a source stage to a destination stage by executing actionIdx.
     *
     * IMPORTANT: The guard witness type may depend on the witnesses contained in [s].
     * We therefore type the guard argument using a dependent match on [s] so that the
     * bound witness variables (w0, w1, ...) are in scope.
     */
    fun stepDecl(fromStage: Int, toStage: Int, actionIdx: Int, actionId: ActionId): String {
        val owner = dag.owner(actionId)
        val anc = ancestorsIdx[actionIdx]
        val fromBinders = bindersForStage[fromStage]
        val toBinders = bindersForStage[toStage]

        val sigArg = "(sig : Signed ${roleCtor[owner]} ${payloadName(actionIdx)})"

        // Pattern match binders from the source state.
        val patBinds = fromBinders.joinToString(" ") { i -> "w$i" }
        val pat = "${stateCtor(fromStage)}${if (patBinds.isBlank()) "" else " $patBinds"}"

        // Guard argument type: depends on the witnesses available in the source state.
        // We write: (g : match s with | stK w0 .. => GuardW_ActionX <anc-ws> sig end)
        val guardBody = if (anc.isEmpty()) {
            "@${guardWName(actionIdx)} sig"
        } else {
            "@${guardWName(actionIdx)} ${anc.joinToString(" ") { a -> "w$a" }} sig"
        }
        val guardArg = buildString {
            append("(g : match s with\n")
            append("  | $pat => $guardBody\n")
            append("  end)")
        }

        val args = listOf(
            "(s : State ${stageName(fromStage)})",
            sigArg,
            guardArg
        ).joinToString("\n  ")

        // Construct the new witness record.
        val newWitRaw =
            "{| ${witSigField(actionIdx)} := sig; ${witGuardField(actionIdx)} := g |}"
        val newWit = "($newWitRaw : ${witnessType(actionIdx)})"

        // Build argument list for the destination constructor (existing witnesses + new one).
        val destArgs = toBinders.joinToString(" ") { i ->
            if (i == actionIdx) newWit else "w$i"
        }

        return buildString {
            appendLine("Definition ${stepFunName(actionIdx, fromStage)}")
            appendLine("  $args")
            appendLine("  : State ${stageName(toStage)} :=")
            appendLine("  match s with")
            appendLine("  | $pat => ${stateCtor(toStage)}${if (destArgs.isBlank()) "" else " $destArgs"}")
            appendLine("  end.")
        }.trimEnd()
    }

    // Build all step functions by exploring transitions between stages.
    data class Transition(val from: Int, val to: Int, val actionIdx: Int, val actionId: ActionId)
    val transitions = mutableListOf<Transition>()
    for ((fromIdx, ds) in stages.withIndex()) {
        for (a in 0 until topo.size) {
            if (ds.contains(a)) continue
            val deps = depsIdx[a]
            if (deps.all { ds.contains(it) }) {
                val next = ds.withAdded(a)
                val toIdx = stageIdOf.getValue(next)
                transitions += Transition(fromIdx, toIdx, a, topo[a])
            }
        }
    }

    // ========== Emit Coq ==========
    val moduleName = coqCtor(game.name.ifBlank { "Game" })
    return buildString {
        appendLine("(* Generated by Vegas: Gallina typestate/runtime (v0, no quits). *)")
        appendLine("From Coq Require Import Bool.Bool.")
        appendLine("From Coq Require Import ZArith.ZArith.")
        appendLine()
        appendLine("Set Implicit Arguments.")
        appendLine("Set Primitive Projections.")
        appendLine()
        appendLine("Module $moduleName.")
        appendLine()

        // Roles
        appendLine("Inductive Role : Type :=")
        roleNames.forEachIndexed { i, rName ->
            val bar = if (i == 0) "|" else "|"
            appendLine("  $bar ${roleCtor[RoleId(rName)]}")
        }
        appendLine(".")
        appendLine()

        // Finite set types
        if (setTypes.isNotEmpty()) {
            val uniq = setTypes.entries
                .sortedBy { it.value }
            for ((t, name) in uniq) {
                appendLine("Inductive $name : Type :=")
                val vals = t.values.sorted()
                vals.forEach { v ->
                    appendLine("| ${name}_v${sanitizeIntCtor(v)}")
                }
                appendLine(".")
                appendLine("Scheme Equality for $name.")
                appendLine()
            }
        }

        // Abstract evidence
        appendLine("Parameter SigW : forall (r : Role) (A : Type) (x : A), Type.")
        appendLine("Record Signed (r : Role) (A : Type) : Type := {")
        appendLine("  msg : A;")
        appendLine("  sig_ok : @SigW r A msg")
        appendLine("}.")
        appendLine()
        appendLine("(* Commitments are kept abstract (may be unused in no-commit games). *)")
        appendLine("Parameter Commitment : Role -> Type -> Type.")
        appendLine("Parameter Opens : forall {r : Role} {A : Type}, Commitment r A -> A -> Type.")
        appendLine()

        // Payloads
        appendLine("(* ---- Action payloads ---- *)")
        for ((i, actionId) in topo.withIndex()) {
            appendLine(payloadDecl(i, actionId))
        }
        appendLine()

        appendLine("(* ---- Action index map ---- *)")
        for ((i, actionId) in topo.withIndex()) {
            val owner = roleCtor[dag.owner(actionId)]
            val deps = depsIdx[i].joinToString(",") { "Action$it" }
            appendLine("(* Action$i: owner=$owner deps=[$deps] *)")
        }
        appendLine()

        // Witnesses + guard witnesses in topo order.
        // IMPORTANT: GuardW_Action<i> may mention W_Action<j> for j<i, and W_Action<i>
        // mentions GuardW_Action<i>. Emitting them interleaved in topo order avoids
        // forward references that Coq rejects.
        appendLine("(* ---- Guard witnesses + Witnesses (full-prefix indices) ---- *)")
        for ((i, actionId) in topo.withIndex()) {
            val owner = dag.owner(actionId)
            val anc = ancestorsIdx[i]

            // Guard witness (abstract) for this action.
            appendLine("Parameter ${guardWName(i)} : ${guardWType(i, owner)}.")

            // Witness record (indexed by full prefix).
            if (anc.isEmpty()) {
                appendLine("Record ${witnessName(i)} : Type := {")
            } else {
                val ancBinders = anc.joinToString(" ") { a -> "(w$a : ${witnessType(a)})" }
                appendLine("Record ${witnessName(i)} $ancBinders : Type := {")
            }
            appendLine("  ${witSigField(i)} : Signed ${roleCtor[owner]} ${payloadName(i)};")

            val sigRef = witSigField(i)
            val guardApp =
                if (anc.isEmpty()) "${guardWName(i)} $sigRef"
                else "@${guardWName(i)} ${anc.joinToString(" ") { a -> "w$a" }} $sigRef"
            appendLine("  ${witGuardField(i)} : $guardApp")
            appendLine("}.")
            appendLine()
        }

        // Stages
        appendLine("(* ---- Runtime stages (down-closed sets of completed actions) ---- *)")
        appendLine("Inductive Stage : Type :=")
        stages.indices.forEach { k ->
            appendLine("| ${stageName(k)}")
        }
        appendLine(".")
        appendLine()

        // State constructors
        appendLine("Inductive State : Stage -> Type :=")
        for ((k, done) in bindersForStage.withIndex()) {
            appendLine(stateCtorDecl(k, done))
        }
        appendLine(".")
        appendLine()

        // Steps
        appendLine("(* ---- Step API ---- *)")
        // Deterministic order: by from-stage, then action index.
        transitions.sortWith(compareBy<Transition>({ it.from }, { it.actionIdx }))
        for (t in transitions) {
            appendLine(stepDecl(t.from, t.to, t.actionIdx, t.actionId))
            appendLine()
        }

        appendLine("End $moduleName.")
    }
}

// =========================================================================
// Internal helpers
// =========================================================================

private fun coqCtor(raw: String): String = coqIdent(raw, upperFirst = true)
private fun coqField(v: VarId): String = coqIdent(v.name, upperFirst = false)

private fun coqIdent(raw: String, upperFirst: Boolean): String {
    val cleaned = buildString {
        for (ch in raw) {
            append(if (ch.isLetterOrDigit() || ch == '_') ch else '_')
        }
    }.trim('_')
    val base = cleaned.ifBlank { "x" }
    val firstOk = base.first().isLetter() || base.first() == '_'
    val prefixed = if (firstOk) base else "x_$base"
    val canon = if (upperFirst) prefixed.replaceFirstChar { it.uppercaseChar() }
    else prefixed.replaceFirstChar { it.lowercaseChar() }
    val reserved = setOf(
        "Type","Prop","Set","Record","Inductive","Definition","Fixpoint","match","with","end",
        "forall","exists","fun","let","in","as","return","if","then","else","Module","End"
    )
    return if (canon in reserved) "v_$canon" else canon
}

private fun sanitizeIntCtor(v: Int): String =
    if (v >= 0) v.toString() else "m${-v}"

private fun collectSetTypes(dag: ActionDag): Map<Type.SetType, Unit> {
    val acc = mutableMapOf<Type.SetType, Unit>()
    for (a in dag.actions) {
        for (p in dag.params(a)) {
            val t = p.type
            if (t is Type.SetType) acc[t] = Unit
        }
    }
    return acc
}

/**
 * Compute transitive prerequisites for each action i (excluding i), as a sorted list of topo indices.
 *
 * Since we are in topo order, a simple DP suffices:
 *   anc[i] = ⋃_{d ∈ deps[i]} (anc[d] ∪ {d}).
 */
private fun computeAncestors(n: Int, deps: List<List<Int>>): List<List<Int>> {
    val ancBits = Array(n) { BitSet(n) }
    for (i in 0 until n) {
        val bs = ancBits[i]
        for (d in deps[i]) {
            bs.or(ancBits[d])
            bs.set(d)
        }
    }
    return (0 until n).map { i ->
        val bs = ancBits[i]
        val out = mutableListOf<Int>()
        var k = bs.nextSetBit(0)
        while (k >= 0) {
            out += k
            k = bs.nextSetBit(k + 1)
        }
        out
    }
}

private data class DoneSet(private val bits: BitSet, private val n: Int) {
    fun contains(i: Int): Boolean = bits.get(i)

    fun withAdded(i: Int): DoneSet {
        val b = bits.clone() as BitSet
        b.set(i)
        return DoneSet(b, n)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DoneSet) return false
        return this.n == other.n && this.bits == other.bits
    }

    override fun hashCode(): Int = 31 * n + bits.hashCode()

    fun size(): Int = bits.cardinality()

    /** Deterministic ordering key: (cardinality, long-array). */
    fun key(): Pair<Int, LongArray> = size() to bits.toLongArray()

    companion object {
        fun empty(n: Int): DoneSet = DoneSet(BitSet(n), n)
    }
}

private fun enumerateDownClosedSets(n: Int, deps: List<List<Int>>): List<DoneSet> {
    val start = DoneSet.empty(n)
    val seen = linkedSetOf(start)
    val q: ArrayDeque<DoneSet> = ArrayDeque()
    q.add(start)
    while (q.isNotEmpty()) {
        val cur = q.removeFirst()
        for (a in 0 until n) {
            if (cur.contains(a)) continue
            if (deps[a].all { cur.contains(it) }) {
                val nxt = cur.withAdded(a)
                if (seen.add(nxt)) q.add(nxt)
            }
        }
    }
    return seen.toList().sortedWith { a, b ->
        val (sa, la) = a.key()
        val (sb, lb) = b.key()
        val c = sa.compareTo(sb)
        if (c != 0) return@sortedWith c
        // Lexicographic compare of long arrays
        val n = minOf(la.size, lb.size)
        for (i in 0 until n) {
            val d = la[i].compareTo(lb[i])
            if (d != 0) return@sortedWith d
        }
        la.size.compareTo(lb.size)
    }

}

private fun makeUnique(names: List<String>): List<String> {
    val seen = mutableMapOf<String, Int>()
    return names.map { n ->
        val k = seen.getOrPut(n) { 0 }
        seen[n] = k + 1
        if (k == 0) n else "${n}_$k"
    }
}

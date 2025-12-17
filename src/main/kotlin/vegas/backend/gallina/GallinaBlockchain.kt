package vegas.backend.gallina

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.Visibility

/**
 * Gallina backend: blockchain-like fair-play runtime + TransitionSpecs.
 *
 * Key idea:
 *   - "Enabled" is derived from deps + fresh + sender/domain/guard proofs.
 *   - No revert: only executions that carry CanExec evidence are considered.
 *
 * Ready for later:
 *   - Quit/timeout via ActStatus + Cell.Null/Hidden and guard witnesses.
 *   - Commit/reveal informationally via Cell.Hidden + guard witnesses relating Hidden/Val.
 */
fun genGallinaBlockchain(game: GameIR): String = GallinaBlockchainGen(game).gen()

private class GallinaBlockchainGen(private val game: GameIR) {
    private val dag: ActionDag = game.dag
    private val topo: List<ActionId> = dag.topo()
    private val idxOf: Map<ActionId, Int> = topo.withIndex().associate { it.value to it.index }

    private val roleIds: List<RoleId> = buildSet {
        game.roles.forEach { add(it) }
        // include owners even if roles list is stale
        dag.actions.forEach { add(dag.owner(it)) }
    }.toList().sortedBy { it.name }

    private val roleCtor: Map<RoleId, String> =
        makeUniqueMap(roleIds.associateWith { coqCtor(it.name) })

    private fun roleCoq(r: RoleId): String = roleCtor.getValue(r)

    // Collect all finite enums (SetType) used anywhere in params.
    private val setTypes: Map<Type.SetType, String> =
        collectSetTypes(dag).keys
            .sortedBy { it.values.sorted().joinToString(",") }
            .mapIndexed { i, t -> t to "T_Set$i" }
            .toMap()

    private fun coqType(t: Type): String = when (t) {
        Type.BoolType -> "bool"
        Type.IntType -> "Z"
        is Type.SetType -> setTypes.getValue(t)
    }

    // Action constructors are canonical Action0..Action(n-1)
    private fun actionCtor(i: Int) = "Action$i"
    private fun argName(i: Int) = "Arg_Action$i"
    private fun enabledName(i: Int) = "Enabled_Action$i"
    private fun guardWName(i: Int) = "GuardW_Action$i"
    private fun packetName(i: Int) = "Packet_Action$i"
    private fun tsName(i: Int) = "TS_Action$i"

    // Keys correspond to global fields (FieldRef(owner,param)).
    private val keyOfField: Map<FieldRef, String> = run {
        val all = linkedMapOf<FieldRef, String>()
        for (a in topo) {
            val owner = dag.owner(a)
            for (p in dag.params(a)) {
                val fr = FieldRef(owner, p.name)
                all.putIfAbsent(fr, coqCtor("K_${owner.name}_${p.name.name}"))
            }
        }
        makeUniqueMap(all)
    }

    private val fieldType: Map<FieldRef, Type> = run {
        val m = mutableMapOf<FieldRef, Type>()
        for (a in topo) {
            val owner = dag.owner(a)
            for (p in dag.params(a)) {
                val fr = FieldRef(owner, p.name)
                val prev = m[fr]
                if (prev != null && prev != p.type) {
                    error("Field $fr has inconsistent types: $prev vs ${p.type}")
                }
                m[fr] = p.type
            }
        }
        m
    }

    private fun keyCtor(fr: FieldRef): String = keyOfField.getValue(fr)

    private fun depsList(i: Int): String {
        val deps = dag.prerequisitesOf(topo[i]).map { idxOf.getValue(it) }.sorted()
        return deps.joinToString("; ", prefix = "[", postfix = "]") { actionCtor(it) }
    }

    // Optional: if the DAG has per-field visibility on an action, use it; else default PUBLIC.
    private fun visibilityOf(action: ActionId, field: FieldRef): Visibility {
        return try {
            val visMap = dag.visibilityOf(action)
            visMap[field] ?: Visibility.PUBLIC
        } catch (_: Throwable) {
            Visibility.PUBLIC
        }
    }

    private fun payloadDecl(i: Int, action: ActionId): String {
        val ps = dag.params(action)
        if (ps.isEmpty()) return "Definition ${argName(i)} : Type := unit."
        val fields = ps.joinToString(";\n") { p ->
            "  ${coqField(p.name, action)} : ${coqType(p.type)}"
        }
        return buildString {
            appendLine("Record ${argName(i)} : Type := {")
            appendLine(fields)
            appendLine("}.")
        }.trimEnd()
    }

    private fun packetDecl(i: Int, action: ActionId): String {
        val ps = dag.params(action)
        if (ps.isEmpty()) {
            return "Definition ${packetName(i)} (_ : ${argName(i)}) : Packet := []."
        }
        // Produce list of existT _ k (Val/Hidden v) depending on visibility.
        // Note: we treat COMMIT as writing Hidden; PUBLIC/REVEAL as writing Val.
        val owner = dag.owner(action)
        val entries = ps.joinToString("; ", prefix = "[", postfix = "]") { p ->
            val fr = FieldRef(owner, p.name)
            val k = keyCtor(fr)
            val v = "a.(${coqField(p.name, action)})"
            val cell = when (visibilityOf(action, fr)) {
                Visibility.COMMIT -> "(Hidden $v)"
                Visibility.PUBLIC, Visibility.REVEAL -> "(Val $v)"
            }
            "(existT _ $k $cell)"
        }
        return "Definition ${packetName(i)} (a : ${argName(i)}) : Packet := $entries."
    }

    private fun enabledDecl(i: Int): String {
        return buildString {
            appendLine("Definition ${enabledName(i)} : EnabledSpec ${argName(i)} :=")
            appendLine("  {| es_deps := ${depsList(i)};")
            appendLine("     es_domain_ok := fun _ => True;")
            appendLine("     es_guardW := ${guardWName(i)} |}.")
        }.trimEnd()
    }

    private fun tsDecl(i: Int, action: ActionId): String {
        val owner = dag.owner(action)
        return buildString {
            appendLine("Definition ${tsName(i)} : TransitionSpec ${argName(i)} :=")
            appendLine("  {| ts_owner := ${roleCoq(owner)};")
            appendLine("     ts_action_id := ${actionCtor(i)};")
            appendLine("     ts_status := Done;")
            appendLine("     ts_enabled := ${enabledName(i)};")
            appendLine("     ts_packet := ${packetName(i)} |}.")
        }.trimEnd()
    }

    fun gen(): String {
        val moduleName = coqCtor(game.name.ifBlank { "Game" })

        return buildString {
            appendLine("(* Generated by Vegas: blockchain-style fair-play runtime + TransitionSpecs. *)")
            appendLine("(* No explicit frontier/ESM: enabledness is derived from deps + evidence. *)")
            appendLine()
            appendLine("From Coq Require Import Bool.Bool.")
            appendLine("From Coq Require Import Lists.List.")
            appendLine("From Coq Require Import Init.Nat.")
            appendLine("From Coq Require Import Logic.Eqdep.")
            appendLine("Import ListNotations.")
            appendLine()
            appendLine("Set Implicit Arguments.")
            appendLine("Set Primitive Projections.")
            appendLine()
            appendLine("Module $moduleName.")
            appendLine()

            // Roles
            appendLine("(* ===================== *)")
            appendLine("(* 1) Roles              *)")
            appendLine("(* ===================== *)")
            appendLine("Inductive Role : Type :=")
            roleIds.forEach { r -> appendLine("| ${roleCoq(r)}") }
            appendLine(".")
            appendLine()

            // Actions
            appendLine("(* ===================== *)")
            appendLine("(* 2) Actions             *)")
            appendLine("(* ===================== *)")
            appendLine("Inductive ActionId : Type :=")
            for (i in topo.indices) appendLine("| ${actionCtor(i)}")
            appendLine(".")
            appendLine("Scheme Equality for ActionId.")
            appendLine()

            // Finite enum types
            if (setTypes.isNotEmpty()) {
                appendLine("(* ===================== *)")
                appendLine("(* 3) Finite enums        *)")
                appendLine("(* ===================== *)")
                for ((t, name) in setTypes.entries.sortedBy { it.value }) {
                    appendLine("Inductive $name : Type :=")
                    for (v in t.values.sorted()) appendLine("| ${name}_v${sanitizeIntCtor(v)}")
                    appendLine(".")
                    appendLine("Scheme Equality for $name.")
                    appendLine()
                }
            }

            // Keys + KeyTy
            appendLine("(* ===================== *)")
            appendLine("(* 4) Storage keys/types  *)")
            appendLine("(* ===================== *)")
            appendLine("Inductive Key : Type :=")
            keyOfField.values.sorted().forEach { k -> appendLine("| $k") }
            appendLine(".")
            appendLine("Scheme Equality for Key.")
            appendLine()

            appendLine("Definition KeyTy (k : Key) : Type :=")
            appendLine("  match k with")
            for ((fr, k) in keyOfField.entries.sortedBy { it.value }) {
                val ty = coqType(fieldType.getValue(fr))
                appendLine("  | $k => $ty")
            }
            appendLine("  end.")
            appendLine()

            // Cells / Store / DoneMap / Env / ChainState
            appendLine("(* ===================== *)")
            appendLine("(* 5) Runtime state       *)")
            appendLine("(* ===================== *)")
            appendLine("Inductive ActStatus : Type := Done | Quit.")
            appendLine()
            appendLine("Inductive Cell (A : Type) : Type :=")
            appendLine("| Unset")
            appendLine("| Val (x : A)")
            appendLine("| Hidden (x : A)")
            appendLine("| Null.")
            appendLine()
            appendLine("Definition DoneMap : Type := ActionId -> option ActStatus.")
            appendLine("Definition Store   : Type := forall k : Key, Cell (KeyTy k).")
            appendLine()
            appendLine("Record Env : Type := { env_dummy : unit }.") // placeholder
            appendLine()
            appendLine("Record ChainState : Type := {")
            appendLine("  cs_env   : Env;")
            appendLine("  cs_done  : DoneMap;")
            appendLine("  cs_store : Store")
            appendLine("}.")
            appendLine()
            appendLine("Definition done_empty  : DoneMap := fun k => None.")
            appendLine("Definition store_empty : Store := fun k => @Unset (KeyTy k).")
            appendLine("Definition init : ChainState :=")
            appendLine("  {| cs_env := {| env_dummy := tt |};")
            appendLine("     cs_done := done_empty;")
            appendLine("     cs_store := store_empty |}.")
            appendLine()

            // EnabledSpec / TransitionSpec
            appendLine("(* ===================== *)")
            appendLine("(* 6) Specs               *)")
            appendLine("(* ===================== *)")
            appendLine("Fixpoint deps_ok (dm : DoneMap) (deps : list ActionId) : Prop :=")
            appendLine("  match deps with")
            appendLine("  | [] => True")
            appendLine("  | a :: ds => dm a = Some Done /\\ deps_ok dm ds")
            appendLine("  end.")
            appendLine()
            appendLine("Record EnabledSpec (Arg : Type) : Type := {")
            appendLine("  es_deps      : list ActionId;")
            appendLine("  es_domain_ok : Arg -> Prop;")
            appendLine("  (* witness-carrying where-clause; later: can depend on timeouts etc via Env *)")
            appendLine("  es_guardW    : Env -> DoneMap -> Store -> Arg -> Type")
            appendLine("}.")
            appendLine()
            appendLine("Definition Packet : Type := list { k : Key & Cell (KeyTy k) }.") // dependent packet
            appendLine()
            appendLine("Record TransitionSpec (Arg : Type) : Type := {")
            appendLine("  ts_owner     : Role;")
            appendLine("  ts_action_id : ActionId;")
            appendLine("  ts_status    : ActStatus;")
            appendLine("  ts_enabled   : EnabledSpec Arg;")
            appendLine("  ts_packet    : Arg -> Packet")
            appendLine("}.")
            appendLine()

            // Fair-play runtime (no revert)
            appendLine("(* ===================== *)")
            appendLine("(* 7) Fair-play exec      *)")
            appendLine("(* ===================== *)")
            appendLine("Record Msg (Arg : Type) : Type := {")
            appendLine("  msg_sender : Role;")
            appendLine("  msg_arg    : Arg")
            appendLine("}.")
            appendLine()
            appendLine("Definition castKeyTy {k1 k2 : Key}")
            appendLine("(H : k2 = k1) (v : Cell (KeyTy k1)) : Cell (KeyTy k2) :=")
            appendLine("  eq_rect _ (fun k => Cell (KeyTy k)) v _ (eq_sym H).")
            appendLine()
            appendLine("Definition store_write (k : Key) (v : Cell (KeyTy k)) (σ : Store) : Store :=")
            appendLine("  fun k' =>")
            appendLine("    match Key_eq_dec k' k with")
            appendLine("    | left H => castKeyTy H v")
            appendLine("    | right _ => σ k'")
            appendLine("    end.")
            appendLine()
            appendLine("Fixpoint store_apply (pkt : Packet) (σ : Store) : Store :=")
            appendLine("  match pkt with")
            appendLine("  | [] => σ")
            appendLine("  | (existT _ k v) :: xs => store_apply xs (store_write k v σ)")
            appendLine("  end.")
            appendLine()
            appendLine("Definition done_set (a : ActionId) (st : ActStatus) (dm : DoneMap) : DoneMap :=")
            appendLine("  fun a' => if ActionId_eq_dec a' a then Some st else dm a'.")
            appendLine()
            appendLine("Record CanExec (Arg : Type) (ts : TransitionSpec Arg) (cs : ChainState) (m : Msg Arg) : Type := {")
            appendLine("  ce_sender_ok : msg_sender m = ts_owner ts;")
            appendLine("  ce_fresh     : cs_done cs (ts_action_id ts) = None;")
            appendLine("  ce_deps_ok   : deps_ok (cs_done cs) (es_deps (ts_enabled ts));")
            appendLine("  ce_domain_ok : es_domain_ok (ts_enabled ts) (msg_arg m);")
            appendLine("  ce_guard_ok  : es_guardW (ts_enabled ts) (cs_env cs) (cs_done cs) (cs_store cs) (msg_arg m)")
            appendLine("}.")
            appendLine()
            appendLine("Definition exec {Arg : Type} (ts : TransitionSpec Arg) (cs : ChainState) (m : Msg Arg)")
            appendLine("  (H : CanExec ts cs m) : ChainState :=")
            appendLine("  let dm' := done_set (ts_action_id ts) (ts_status ts) (cs_done cs) in")
            appendLine("  let σ'  := store_apply (ts_packet ts (msg_arg m)) (cs_store cs) in")
            appendLine("  {| cs_env := cs_env cs; cs_done := dm'; cs_store := σ' |}.")
            appendLine()

            // Per-action Arg types
            appendLine("(* ===================== *)")
            appendLine("(* 8) Action arguments    *)")
            appendLine("(* ===================== *)")
            for ((i, a) in topo.withIndex()) {
                appendLine(payloadDecl(i, a))
            }
            appendLine()

            // Per-action guard witnesses (abstract), enabled specs, packets, TS
            appendLine("(* ===================== *)")
            appendLine("(* 9) Transition specs    *)")
            appendLine("(* ===================== *)")
            for ((i, a) in topo.withIndex()) {
                appendLine("Parameter ${guardWName(i)} : Env -> DoneMap -> Store -> ${argName(i)} -> Type.")
                appendLine(packetDecl(i, a))
                appendLine(enabledDecl(i))
                appendLine(tsDecl(i, a))
                appendLine()
            }

            // Helpful comment: action map
            appendLine("(* ---- Action index map (for humans) ---- *)")
            for ((i, a) in topo.withIndex()) {
                val owner = roleCoq(dag.owner(a))
                val deps = dag.prerequisitesOf(a).map { idxOf.getValue(it) }.sorted()
                    .joinToString(",") { "Action$it" }
                appendLine("(* Action$i: owner=$owner deps=[$deps] *)")
            }
            appendLine()

            appendLine("End $moduleName.")
        }
    }
}

/* ----------------- helpers ----------------- */

private fun coqCtor(raw: String): String = coqIdent(raw, upperFirst = true)
private fun coqField(v: VarId, action: ActionId): String = coqIdent("${action}${v.name}", upperFirst = false)

private fun coqIdent(raw: String, upperFirst: Boolean): String {
    val cleaned = buildString {
        for (ch in raw) append(if (ch.isLetterOrDigit() || ch == '_') ch else '_')
    }.trim('_')
    val base = cleaned.ifBlank { "x" }
    val firstOk = base.first().isLetter() || base.first() == '_'
    val prefixed = if (firstOk) base else "x_$base"
    val canon =
        if (upperFirst) prefixed.replaceFirstChar { it.uppercaseChar() }
        else prefixed.replaceFirstChar { it.lowercaseChar() }

    val reserved = setOf(
        "Type","Prop","Set","Record","Inductive","Definition","Fixpoint","match","with","end",
        "forall","exists","fun","let","in","as","return","if","then","else","Module","End"
    )
    val res = if (canon in reserved) "v_$canon" else canon
    return res.replace("__", "_")
}

private fun sanitizeIntCtor(v: Int): String = if (v >= 0) v.toString() else "m${-v}"

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

/** Ensure all generated Coq names are unique (stable suffixing). */
private fun <K> makeUniqueMap(m: Map<K, String>): Map<K, String> {
    val seen = mutableMapOf<String, Int>()
    val out = LinkedHashMap<K, String>()
    for ((k, v) in m) {
        val c = seen.getOrPut(v) { 0 }
        seen[v] = c + 1
        out[k] = if (c == 0) v else "${v}_$c"
    }
    return out
}

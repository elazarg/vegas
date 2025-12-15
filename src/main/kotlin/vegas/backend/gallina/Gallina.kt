package vegas.backend.gallina

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.*
import vegas.dag.FrontierMachine
import vegas.dag.Dag

fun generateGallina(ir: GameIR): String {
    return GallinaGenerator(ir).generate()
}

/**
 * Generates Coq/Gallina code for the given GameIR.
 *
 * Goals:
 * 1. Define Roles and Domain Types.
 * 2. Define Abstract Evidence (SigW, Signed).
 * 3. Define Payloads (Action contents).
 * 4. Define Witnesses (Evidence of actions + dependencies + guards).
 * 5. Define State Machine (Stage, State, Steps).
 */
private class GallinaGenerator(val ir: GameIR) {
    val sb = StringBuilder()
    val dag = ir.dag
    val topoSorted = dag.topo()

    // Map ActionId to a readable name
    val actionNames: Map<ActionId, String> = dag.actions.associateWith { id ->
        val role = dag.owner(id)
        val spec = dag.spec(id)
        // Try to find a meaningful name from parameters or role
        // For reveal, we usually want "Reveal" + param
        // For commit, "Commit" + param
        // For join, "Join"
        val base = when (dag.kind(id)) {
            Visibility.COMMIT -> "Commit"
            Visibility.REVEAL -> "Reveal"
            Visibility.PUBLIC -> if (spec.join != null) "Join" else "Move"
        }

        // Add unique suffix if multiple actions of same kind
        // Or include parameter name if available
        val params = spec.params.map { it.name.name }
        val suffix = if (params.isNotEmpty()) params.joinToString("") { it.capitalize() } else ""

        "${role.name}${base}${suffix}"
    }

    // Map RoleId to Coq constructor name
    fun roleName(r: RoleId) = r.name

    // Helper for indentation
    var indentLevel = 0
    fun line(s: String = "") {
        sb.append("  ".repeat(indentLevel)).append(s).append("\n")
    }

    fun generate(): String {
        line("From Coq Require Import Bool.Bool.")
        line("From Coq Require Import ZArith.ZArith.")
        line("From Coq Require Import List.")
        line("Import ListNotations.")
        line()
        line("Set Implicit Arguments.")
        line("Set Primitive Projections.")
        line()
        line("Module ${ir.name}_Protocol.")
        line()

        generateRolesAndTypes()
        generateAbstractEvidence()
        generateActionPayloads()
        generateWitnesses()
        generateStateMachine()

        line("End ${ir.name}_Protocol.")
        return sb.toString()
    }

    fun generateRolesAndTypes() {
        line("(* ===================== *)")
        line("(* 1) Roles, Types       *)")
        line("(* ===================== *)")
        line()

        // Roles
        val roles = ir.roles.sortedBy { it.name }
        line("Inductive Role : Type := ${roles.joinToString(" | ")}")
        line("Scheme Equality for Role.")
        line()

        // Domain Types
        // We scan all params to find SetTypes and aliased types
        // Sort to ensure determinism
        val paramTypes = dag.metas.flatMap { it.spec.params.map { p -> p.type } }.toSet()
            .sortedBy { typeToCoq(it) }

        for (t in paramTypes) {
            when (t) {
                is Type.SetType -> generateSetType(t)
                else -> {}
            }
        }
    }

    fun generateSetType(t: Type.SetType) {
        // We name the type based on usage if possible, but here we only have the structure.
        // We might need a global type registry or heuristics.
        // For now, let's map known shapes (like 0,1,2 -> Door) or generate generic names.
        // Since `ir` doesn't preserve type aliases, we check if we can infer or if we just dump "Enum_..."
        // User example used "Door".
        // In Vegas IR, we don't strictly have type names for SetTypes unless we look at the AST or heuristics.
        // Best effort: Enum_vals
        val vals = t.values.sorted()
        val name = "Enum_" + vals.joinToString("_")
        val ctors = vals.map { "E$it" }
        line("Inductive $name : Type := ${ctors.joinToString(" | ")}.")
        line("Scheme Equality for $name.")
        line()
    }

    fun typeToCoq(t: Type): String = when(t) {
        Type.BoolType -> "bool"
        Type.IntType -> "Z"
        is Type.SetType -> "Enum_" + t.values.sorted().joinToString("_") // Must match generateSetType
    }

    fun generateAbstractEvidence() {
        line("(* ===================== *)")
        line("(* 2) Abstract evidence  *)")
        line("(* ===================== *)")
        line()
        line("Parameter SigW : forall (r : Role) (A : Type), A -> Type.")
        line()
        line("Record Signed (r : Role) (A : Type) : Type := {")
        line("  msg : A;")
        line("  sig_ok : SigW r A msg")
        line("}.")
        line()
        line("Parameter Commitment : Role -> Type -> Type.")
        line("Parameter Opens : forall {r : Role} {A : Type}, Commitment r A -> A -> Type.")
        line()
    }

    fun generateActionPayloads() {
        line("(* ===================== *)")
        line("(* 3) Action payloads    *)")
        line("(* ===================== *)")
        line()

        for (id in topoSorted) {
            val name = "P_" + actionNames[id]!!
            val spec = dag.spec(id)
            val struct = dag.meta(id).struct

            // If Commit
            if (dag.kind(id) == Visibility.COMMIT) {
                // Find what is being committed
                // The commit payload contains "Commitment Role Type"
                // We need to find the type of the hidden field.
                // commitFields gives us the names. We need the types from the params of the original action?
                // Wait, in expanded DAG, the commit action has params?
                // spec.params on a COMMIT node are usually empty or matching the original?
                // In `expandCommitReveal`: "Commit spec: trivial guard". Params are kept?
                // No, "params" are not explicitly cleared in `expandCommitReveal`.
                // However, the *logic* is that the commit payload contains the commitment, not the values.

                // Let's assume for each hidden param, we have a commitment.
                // Or just one commitment for the whole tuple?
                // User example: `Record P_Commit : Type := { com : Commitment Host Door }.`
                // It commits to a Door.

                // In Vegas, a commit hides specific fields.
                // We generate one commitment field per hidden parameter.

                line("Record $name : Type := {")
                indentLevel++
                for (f in struct.commitFields) {
                    // Find type of f
                    // f is (Role, Name). It refers to a parameter of *this* action (or previous?).
                    // Fields written by this action are in `struct.writes`.
                    // The type is in `spec.params`.
                    val param = spec.params.find { it.name == f.param }
                        ?: error("Written field ${f} not found in params of $id")
                    line("com_${f.param.name} : Commitment ${roleName(struct.owner)} ${typeToCoq(param.type)};")
                }
                indentLevel--
                line("}.")
            }
            // If Reveal
            else if (dag.kind(id) == Visibility.REVEAL) {
                 // Reveal payload contains the actual values.
                 line("Record $name : Type := {")
                 indentLevel++
                 for (f in struct.revealFields) {
                     val param = spec.params.find { it.name == f.param }
                         ?: error("Written field ${f} not found in params of $id")
                     line("${f.param.name} : ${typeToCoq(param.type)};")
                 }
                 indentLevel--
                 line("}.")
            }
            // If Public
            else {
                if (spec.params.isEmpty()) {
                     line("Definition $name : Type := unit.")
                } else {
                    line("Record $name : Type := {")
                    indentLevel++
                    for (p in spec.params) {
                        line("${p.name.name} : ${typeToCoq(p.type)};")
                    }
                    indentLevel--
                    line("}.")
                }
            }
            line()
        }
    }

    // Witness Name for an action
    fun witnessName(id: ActionId) = "W_" + actionNames[id]!!

    // The "history" arguments for a witness or state constructor
    // Returns list of (argName, typeName)
    fun historyArgs(id: ActionId): List<Pair<String, String>> {
        // Collect all ancestors in topo order
        val ancestors = dag.ancestorsOf(id).sortedBy { topoSorted.indexOf(it) }
        return ancestors.map { anc ->
            val wName = witnessName(anc)
            // The witness type depends on *its* ancestors.
            // So we need to pass the variable names of *its* ancestors.
            // This suggests we need a consistent naming scheme for variables of type Witness.
            // Let's use `w_{ActionName}`.
            val varName = "w_" + actionNames[anc]!!

            // Construct the type application: W_Ancestor arg1 arg2 ...
            // The args are the variables corresponding to the ancestors of 'anc'.
            val ancAncestors = dag.ancestorsOf(anc).sortedBy { topoSorted.indexOf(it) }
            val args = ancAncestors.map { "w_" + actionNames[it]!! }.joinToString(" ")

            varName to (if (args.isEmpty()) wName else "($wName $args)")
        }
    }

    // Find the action that exposes the value of a field (Public or Reveal)
    // Returns null if the field is currently hidden (only committed)
    fun findValueWriter(field: FieldRef): ActionId? {
        return dag.actions.find { id ->
            val s = dag.meta(id).struct
            s.writes.contains(field) && (s.visibility[field] == Visibility.PUBLIC || s.visibility[field] == Visibility.REVEAL)
        }
    }

    fun generateWitnesses() {
        line("(* ===================== *)")
        line("(* 4) Witnesses          *)")
        line("(* ===================== *)")
        line()

        for (id in topoSorted) {
            val wName = witnessName(id)
            val pName = "P_" + actionNames[id]!!
            val role = dag.owner(id)

            val args = historyArgs(id)
            val argDecl = args.joinToString(" ") { "(${it.first} : ${it.second})" }

            line("Record $wName $argDecl : Type := {")
            indentLevel++
            line("sig_${actionNames[id]} : Signed ${roleName(role)} $pName;")

            // Add opening checks for Reveals
            if (dag.kind(id) == Visibility.REVEAL) {
                val struct = dag.meta(id).struct
                for (f in struct.revealFields) {
                     // Find the commit action for this field
                     // We need to search ancestors for the COMMIT of this field
                     val commitId = dag.ancestorsOf(id).find { anc ->
                         dag.meta(anc).struct.commitFields.contains(f)
                     } ?: error("No commit found for reveal of $f at $id")

                     val commitVar = "w_" + actionNames[commitId]!!
                     // Path to commitment: commitVar.(sig_...).msg.(com_Param)
                     val comPath = "$commitVar.(sig_${actionNames[commitId]}).(msg).(com_${f.param.name})"
                     // Path to value: sig_This.msg.Param
                     val valPath = "sig_${actionNames[id]}.(msg).(${f.param.name})"

                     line("opening_${f.param.name} : Opens $comPath $valPath;")
                }
            }

            // Add Guard Expressions
            val guard = dag.spec(id).guardExpr
            if (guard !is Expr.Const.BoolVal || !guard.v) {
                 // Generate Coq prop for guard
                 // We need a helper to translate Expr to Coq term, resolving fields to Witness accessors
                 line("guard : ${exprToCoq(guard, args.map { it.first }.toSet(), id)};")
            }

            indentLevel--
            line("}.")
            line()
        }
    }

    // Translate Expr to Coq
    // contextVars is the set of available witness variables (e.g. "w_HostJoin")
    fun exprToCoq(e: Expr, contextVars: Set<String>, currentAction: ActionId? = null): String {
        return when(e) {
            is Expr.Const.IntVal -> "${e.v}%Z"
            is Expr.Const.BoolVal -> if (e.v) "true" else "false"
            is Expr.Const.Hidden -> exprToCoq(e.inner, contextVars, currentAction)
            Expr.Const.Opaque -> "0%Z" // Should not happen in guard?
            Expr.Const.Quit -> "false"
            is Expr.Field -> {
                // Find which action wrote this field value
                val writer = findValueWriter(e.field)

                if (writer == null) {
                    return "true (* hidden field ${e.field} *)"
                }

                // If the writer is the current action
                if (currentAction != null && writer == currentAction) {
                    return "sig_${actionNames[currentAction]}.(msg).(${e.field.param.name})"
                }

                val wName = "w_" + actionNames[writer]!!
                if (wName !in contextVars && writer !in topoSorted) {
                     // This could happen if we are referencing a future/concurrent field?
                     // In valid Vegas DAGs, dependencies should be in context.
                     error("Field ${e.field} written by $writer which is not in context $contextVars")
                }

                // Construct path: w_Writer.(sig_...).msg.Field
                "$wName.(sig_${actionNames[writer]}).(msg).(${e.field.param.name})"
            }
            is Expr.IsDefined -> "true" // Assume defined if witness exists
            is Expr.Eq -> "(${exprToCoq(e.l, contextVars, currentAction)} = ${exprToCoq(e.r, contextVars, currentAction)})"
            is Expr.Ne -> "(${exprToCoq(e.l, contextVars, currentAction)} <> ${exprToCoq(e.r, contextVars, currentAction)})"
            is Expr.And -> "(andb ${exprToCoq(e.l, contextVars, currentAction)} ${exprToCoq(e.r, contextVars, currentAction)})"
            is Expr.Or -> "(orb ${exprToCoq(e.l, contextVars, currentAction)} ${exprToCoq(e.r, contextVars, currentAction)})"
            is Expr.Not -> "(negb ${exprToCoq(e.x, contextVars, currentAction)})"
            // Arithmetic
            is Expr.Add -> "(${exprToCoq(e.l, contextVars, currentAction)} + ${exprToCoq(e.r, contextVars, currentAction)})%Z"
            is Expr.Sub -> "(${exprToCoq(e.l, contextVars, currentAction)} - ${exprToCoq(e.r, contextVars, currentAction)})%Z"
            else -> "true (* expr not supported yet: $e *)"
        }
    }

    fun generateStateMachine() {
        line("(* ===================== *)")
        line("(* 5) Typed runtime/ESM  *)")
        line("(* ===================== *)")
        line()

        // We need to explore reachable sets of actions (frontier).
        // Since we don't have the explicit state machine generic solver handy in this class,
        // we can use `FrontierMachine` to simulate.

        // But `FrontierMachine` just tells us what is enabled.
        // We need to explore the graph of states (sets of executed actions).

        val visited = mutableSetOf<Set<ActionId>>()
        val queue = ArrayDeque<Set<ActionId>>()
        val transitions = mutableListOf<Triple<Set<ActionId>, ActionId, Set<ActionId>>>()

        val initial = emptySet<ActionId>()
        queue.add(initial)
        visited.add(initial)

        // Map State (Set<ActionId>) to a name
        val stateNames = mutableMapOf<Set<ActionId>, String>()
        var stateCounter = 0
        stateNames[initial] = "S0"

        while (queue.isNotEmpty()) {
            val current = queue.removeFirst()

            // Find enabled actions
            // An action is enabled if all its prereqs are in `current`
            // AND it is not in `current`
            val enabled = dag.actions.filter { action ->
                action !in current && dag.prerequisitesOf(action).all { it in current }
            }

            for (act in enabled) {
                val next = current + act
                transitions.add(Triple(current, act, next))

                if (next !in visited) {
                    visited.add(next)
                    queue.add(next)
                    // Generate name
                    stateCounter++
                    stateNames[next] = "S$stateCounter"
                }
            }
        }

        // 1. Stage Inductive
        // Sort states by size/topo roughly
        val sortedStates = stateNames.entries.sortedBy { it.value.removePrefix("S").toInt() }
        line("Inductive Stage : Type :=")
        line(sortedStates.joinToString(" | ") { it.value } + ".")
        line()

        // 2. State Type Family
        line("Inductive State : Stage -> Type :=")
        for ((stateSet, sName) in sortedStates) {
            val constructorName = "st${sName.removePrefix("S")}"
            // Arguments: Witnesses for all actions in stateSet
            // Sorted by topo to match dependencies
            val acts = topoSorted.filter { it in stateSet }

            // We need to build the arguments list: (w_Act : W_Act args...)
            val args = acts.map { act ->
                 val wType = witnessName(act)
                 val wVar = "w_" + actionNames[act]!!
                 val wDeps = historyArgs(act) // this returns variable names of ancestors
                 // The ancestors are guaranteed to be in `acts` (and thus `stateSet`) because of closed property
                 val wApp = if (wDeps.isEmpty()) wType else "($wType ${wDeps.joinToString(" ") { it.first }})"
                 "($wVar : $wApp)"
            }

            val arrow = if (args.isEmpty()) "" else args.joinToString(" ") + " -> "
            line("| $constructorName : ${arrow}State $sName")
        }
        line(".")
        line()

        // 3. Step Functions
        line("(* Step API *)")
        for ((src, act, dst) in transitions) {
            val srcName = stateNames[src]!!
            val dstName = stateNames[dst]!!
            val funcName = "step_" + actionNames[act]!!.lowercase() + "_from_" + srcName.lowercase()

            val actName = actionNames[act]!!
            val wName = witnessName(act)
            val pName = "P_" + actName

            line("Definition $funcName (s : State $srcName) (sig : Signed ${roleName(dag.owner(act))} $pName)")

            // Add guard arguments
            val guard = dag.spec(act).guardExpr
            if (guard !is Expr.Const.BoolVal || !guard.v) {
                sb.append("  (Hguard : ")
                sb.append(exprToCoqStep(guard, src, srcName, act))
                sb.append(")")
            }

            // Add Open proofs for Reveal
            if (dag.kind(act) == Visibility.REVEAL) {
                 val struct = dag.meta(act).struct
                 for (f in struct.revealFields) {
                      sb.append("\n  (Hopen_${f.param.name} : ")
                      // Opens (match s ... commit ... ) sig.msg.val
                      // Find commit writer
                      val commitId = dag.ancestorsOf(act).find { anc -> dag.meta(anc).struct.commitFields.contains(f) }!!
                      val cWriter = "w_" + actionNames[commitId]!!

                      val commitExpr = "(match s with ${matchPattern(src, srcName)} => $cWriter.(sig_${actionNames[commitId]}).(msg).(com_${f.param.name}) end)"
                      val valExpr = "sig.(msg).(${f.param.name})"
                      sb.append("Opens $commitExpr $valExpr)")
                 }
            }

            line(" : State $dstName :=")
            line("  match s with")
            line("  | ${matchPattern(src, srcName)} =>")

            // Construct new witness
            // {| sig_Action := sig; guard := Hguard; ... |}
            var recFields = "sig_${actName} := sig"
            if (guard !is Expr.Const.BoolVal || !guard.v) {
                recFields += "; guard := Hguard"
            }
            if (dag.kind(act) == Visibility.REVEAL) {
                val struct = dag.meta(act).struct
                for (f in struct.revealFields) {
                    recFields += "; opening_${f.param.name} := Hopen_${f.param.name}"
                }
            }

            val newWitness = "{| $recFields |}"

            // Construct destination state

            val dstActs = topoSorted.filter { it in dst }
            val appArgs = dstActs.map { a ->
                if (a == act) newWitness else "w_" + actionNames[a]!!
            }

            line("      st${dstName.removePrefix("S")} ${appArgs.joinToString(" ")}")
            line("  end.")
            line()
        }
    }

    // Helper to generate pattern: stSrc w_Act1 w_Act2 ...
    fun matchPattern(state: Set<ActionId>, stateName: String): String {
        if (state.isEmpty()) return "st${stateName.removePrefix("S")}"

        val acts = topoSorted.filter { it in state }
        val vars = acts.map { "w_" + actionNames[it]!! }
        return "st${stateName.removePrefix("S")} ${vars.joinToString(" ")}"
    }

    fun exprToCoqStep(e: Expr, state: Set<ActionId>, stateName: String, currentAction: ActionId): String {
        return when(e) {
            is Expr.Const.IntVal -> "${e.v}%Z"
            is Expr.Const.BoolVal -> if (e.v) "true" else "false"
            is Expr.Const.Hidden -> exprToCoqStep(e.inner, state, stateName, currentAction)
            is Expr.Field -> {
                val writer = findValueWriter(e.field)

                if (writer == null) {
                    return "true (* hidden field ${e.field} *)"
                }

                if (writer in state) {
                    // Extract from state
                     val wName = "w_" + actionNames[writer]!!
                     val accessor = "$wName.(sig_${actionNames[writer]}).(msg).(${e.field.param.name})"
                     "(match s with ${matchPattern(state, stateName)} => $accessor end)"
                } else if (writer == currentAction) {
                    // Must be from current signal?
                    "sig.(msg).(${e.field.param.name})"
                } else {
                     return "true (* future/hidden field ${e.field} *)"
                }
            }
            is Expr.Eq -> "(${exprToCoqStep(e.l, state, stateName, currentAction)} = ${exprToCoqStep(e.r, state, stateName, currentAction)})"
            is Expr.Ne -> "(${exprToCoqStep(e.l, state, stateName, currentAction)} <> ${exprToCoqStep(e.r, state, stateName, currentAction)})"
            is Expr.And -> "(andb ${exprToCoqStep(e.l, state, stateName, currentAction)} ${exprToCoqStep(e.r, state, stateName, currentAction)})"
            is Expr.Or -> "(orb ${exprToCoqStep(e.l, state, stateName, currentAction)} ${exprToCoqStep(e.r, state, stateName, currentAction)})"
            is Expr.Not -> "(negb ${exprToCoqStep(e.x, state, stateName, currentAction)})"
            // Arithmetic
            is Expr.Add -> "(${exprToCoqStep(e.l, state, stateName, currentAction)} + ${exprToCoqStep(e.r, state, stateName, currentAction)})%Z"
            is Expr.Sub -> "(${exprToCoqStep(e.l, state, stateName, currentAction)} - ${exprToCoqStep(e.r, state, stateName, currentAction)})%Z"
            else -> "true"
        }
    }
}

fun String.capitalize() = this.replaceFirstChar { if (it.isLowerCase()) it.titlecase() else it.toString() }

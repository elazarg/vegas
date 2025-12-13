package vegas.backend.smt

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.GameIR
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.Type
import vegas.ir.Visibility
import vegas.ir.ActionDag

enum class SmtMode {
    SATISFIABILITY, // QF-SMT: Flat constants, single trace existence
    STRATEGY        // DQBF/Skolem: Functions of dependencies, strategy existence
}

fun generateSMT(ir: GameIR): String = generate(ir, SmtMode.SATISFIABILITY, null)

fun generateDQBF(ir: GameIR, coalition: Set<RoleId>? = null): String =
    generate(ir, SmtMode.STRATEGY, coalition)

private fun generate(ir: GameIR, mode: SmtMode, coalition: Set<RoleId>?): String {
    return SmtGenerator(ir, mode, coalition).run()
}

private class SmtGenerator(
    val ir: GameIR,
    val mode: SmtMode,
    val coalition: Set<RoleId>?
) {
    val dag = ir.dag
    val sb = StringBuilder()

    // 1. Collect all parameter types
    val paramTypes: Map<FieldRef, Type> = dag.metas
        .flatMap { meta -> meta.spec.params.map { param -> FieldRef(meta.struct.owner, param.name) to param.type } }
        .toMap()

    // 2. Identify all fields referenced
    val referencedFields = mutableSetOf<FieldRef>().apply {
        dag.metas.forEach { meta -> addAll(collectFields(meta.spec.guardExpr)) }
        ir.payoffs.values.forEach { expr -> addAll(collectFields(expr)) }
        dag.actions.forEach { id -> addAll(dag.writes(id)) }
    }

    val allFields = referencedFields.associateWith { field ->
        paramTypes[field] ?: Type.IntType
    }

    // 3. Pre-calculate dependencies for Strategy mode
    val actionDependencies: Map<ActionId, List<FieldRef>> = if (mode == SmtMode.STRATEGY) {
        dag.actions.associateWith { id ->
            val owner = dag.owner(id)
            val ancestors = dag.ancestorsOf(id)
            val visible = mutableSetOf<FieldRef>()

            for (anc in ancestors) {
                val struct = dag.meta(anc).struct
                visible.addAll(struct.publicFields)
                visible.addAll(struct.revealFields)
                if (struct.owner == owner) {
                    visible.addAll(struct.commitFields)
                }
            }
            visible.sortedBy { "${it.owner}_${it.param}" }
        }
    } else {
        emptyMap()
    }

    val fieldWriter = mutableMapOf<FieldRef, ActionId>().apply {
        dag.actions.forEach { id ->
            dag.writes(id).forEach { field ->
                val vis = dag.visibilityOf(id)[field]
                if (vis == Visibility.PUBLIC || vis == Visibility.COMMIT) {
                    put(field, id)
                }
            }
        }
    }

    fun run(): String {
        val sortedActions = dag.topo()
        val universalVars = mutableListOf<String>()
        val assumptions = mutableListOf<String>()
        val guarantees = mutableListOf<String>()

        if (mode == SmtMode.SATISFIABILITY) {
            allFields.forEach { (field, type) ->
                sb.appendLine("(declare-const ${fieldName(field)} ${smtType(type)})")
                sb.appendLine("(declare-const ${doneFieldName(field)} Bool)")
                val domain = getDomainConstraint(field, type, fieldName(field))
                if (domain != null) sb.appendLine("(assert $domain)")
                sb.appendLine()
            }
            sortedActions.forEach { id ->
                sb.appendLine("(declare-const ${actionDoneName(id)} Bool)")
            }
        } else {
            // Strategy Mode Declarations
            sortedActions.forEach { id ->
                val owner = dag.owner(id)
                val isUniversal = coalition != null && owner !in coalition
                val deps = actionDependencies[id] ?: emptyList()

                if (isUniversal) {
                    universalVars.add("(${actionDoneName(id)} Bool)")
                    dag.writes(id).forEach { field ->
                         if (allFields.containsKey(field)) {
                             val type = allFields[field]!!
                             universalVars.add("(${fieldName(field)} ${smtType(type)})")
                             universalVars.add("(${doneFieldName(field)} Bool)")
                         }
                    }
                } else {
                    val depTypes = deps.flatMap { f ->
                        listOf(smtType(allFields[f] ?: Type.IntType), "Bool")
                    }.joinToString(" ")

                    sb.appendLine("(declare-fun ${actionDoneName(id)} ($depTypes) Bool)")

                    dag.writes(id).forEach { field ->
                         if (allFields.containsKey(field)) {
                             val type = allFields[field]!!
                             sb.appendLine("(declare-fun ${fieldName(field)} ($depTypes) ${smtType(type)})")
                             sb.appendLine("(declare-fun ${doneFieldName(field)} ($depTypes) Bool)")
                         }
                    }
                }
            }
        }

        // Generate Assertions
        sortedActions.forEach { id ->
            val contextId = if (mode == SmtMode.STRATEGY) id else null

            val actDone = resolveActionDone(id, contextId)
            val prereq = dag.prerequisitesOf(id).map { resolveActionDone(it, contextId) }
            val prereqExpr = prereq.fold("true") { acc, name -> "(and $acc $name)" }

            val guard = dag.spec(id).guardExpr
            val guardExpr = exprToSmt(guard, { f -> resolveField(f, contextId) }, { f -> resolveDone(f, contextId) })

            val constraint = "(=> $actDone (and $prereqExpr $guardExpr))"

            val owner = dag.owner(id)
            val isUniversal = coalition != null && owner !in coalition

            if (isUniversal) assumptions.add(constraint) else guarantees.add(constraint)

            dag.writes(id).forEach { field ->
                val fDone = resolveDone(field, contextId)
                val wrConstraint = "(=> $actDone $fDone)"

                if (isUniversal) assumptions.add(wrConstraint) else guarantees.add(wrConstraint)

                if (mode == SmtMode.STRATEGY && allFields.containsKey(field)) {
                     val type = allFields[field]!!
                     val domain = getDomainConstraint(field, type, resolveField(field, contextId))
                     if (domain != null) {
                         if (isUniversal) assumptions.add(domain) else guarantees.add(domain)
                     }
                }
            }
        }

        // Payoffs / Outcomes
        if (mode == SmtMode.SATISFIABILITY) {
            ir.payoffs.forEach { (role, expr) ->
                sb.appendLine("(declare-const ${outcomeName(role)} Int)")
                sb.appendLine("(assert (= ${outcomeName(role)} ${exprToSmt(expr, { fieldName(it) }, { doneFieldName(it) })}))")
            }
        }

        // Emit Assertions
        if (mode == SmtMode.STRATEGY && universalVars.isNotEmpty()) {
            val assumptionsExpr = if (assumptions.isEmpty()) "true" else "(and\n    ${assumptions.joinToString("\n    ")})"
            val guaranteesExpr = if (guarantees.isEmpty()) "true" else "(and\n    ${guarantees.joinToString("\n    ")})"

            sb.appendLine("(assert (forall (${universalVars.joinToString(" ")})")
            sb.appendLine("  (=> $assumptionsExpr")
            sb.appendLine("      $guaranteesExpr)")
            sb.appendLine("))")
        } else {
            assumptions.forEach { sb.appendLine("(assert $it)") }
            guarantees.forEach { sb.appendLine("(assert $it)") }
        }

        sb.appendLine("(check-sat)")
        if (mode == SmtMode.SATISFIABILITY) {
            sb.appendLine("(get-model)")
        }

        return sb.toString()
    }

    fun resolveField(field: FieldRef, contextId: ActionId?): String {
        if (mode == SmtMode.SATISFIABILITY) return fieldName(field)

        val writerId = fieldWriter[field] ?: error("Unknown writer for $field")
        val owner = dag.owner(writerId)
        val isUniversal = coalition != null && owner !in coalition

        if (isUniversal) return fieldName(field)

        val writerDeps = actionDependencies[writerId] ?: emptyList()
        val args = writerDeps.joinToString(" ") { dep ->
             "${resolveField(dep, contextId)} ${resolveDone(dep, contextId)}"
        }
        return if (args.isEmpty()) fieldName(field) else "(${fieldName(field)} $args)"
    }

    fun resolveDone(field: FieldRef, contextId: ActionId?): String {
         if (mode == SmtMode.SATISFIABILITY) return doneFieldName(field)

         val writerId = fieldWriter[field] ?: error("Unknown writer for $field")
         val owner = dag.owner(writerId)
         val isUniversal = coalition != null && owner !in coalition

         if (isUniversal) return doneFieldName(field)

         val writerDeps = actionDependencies[writerId] ?: emptyList()
         val args = writerDeps.joinToString(" ") { dep ->
              "${resolveField(dep, contextId)} ${resolveDone(dep, contextId)}"
         }
         return if (args.isEmpty()) doneFieldName(field) else "(${doneFieldName(field)} $args)"
    }

    fun resolveActionDone(id: ActionId, contextId: ActionId?): String {
        if (mode == SmtMode.SATISFIABILITY) return actionDoneName(id)

        val owner = dag.owner(id)
        val isUniversal = coalition != null && owner !in coalition
        if (isUniversal) return actionDoneName(id)

        val deps = actionDependencies[id] ?: emptyList()
        val args = deps.joinToString(" ") { dep ->
             "${resolveField(dep, contextId)} ${resolveDone(dep, contextId)}"
        }
        return if (args.isEmpty()) actionDoneName(id) else "(${actionDoneName(id)} $args)"
    }
}

private fun getDomainConstraint(field: FieldRef, type: Type, term: String): String? {
    return when (type) {
        is Type.SetType -> {
            if (type.values.isNotEmpty()) {
                val clauses = type.values.sorted().joinToString(" ") { v -> "(= $term $v)" }
                "(or $clauses)"
            } else null
        }
        else -> null
    }
}

private fun exprToSmt(
    e: Expr,
    fieldMapper: (FieldRef) -> String,
    doneMapper: (FieldRef) -> String
): String = when (e) {
    is Expr.Const.IntVal -> "${e.v}"
    is Expr.Const.BoolVal -> "${e.v}"
    is Expr.Const.Hidden -> exprToSmt(e.inner, fieldMapper, doneMapper)
    Expr.Const.Opaque -> "0"
    Expr.Const.Quit -> "false"
    is Expr.Field -> fieldMapper(e.field)
    is Expr.IsDefined -> doneMapper(e.field)
    is Expr.Add -> "(+ ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Sub -> "(- ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Mul -> "(* ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Div -> "(div ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Mod -> "(mod ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Neg -> "(- ${exprToSmt(e.x, fieldMapper, doneMapper)})"
    is Expr.Eq -> "(= ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Ne -> "(not (= ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)}))"
    is Expr.Lt -> "(< ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Le -> "(<= ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Gt -> "(> ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Ge -> "(>= ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.And -> "(and ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Or -> "(or ${exprToSmt(e.l, fieldMapper, doneMapper)} ${exprToSmt(e.r, fieldMapper, doneMapper)})"
    is Expr.Not -> "(not ${exprToSmt(e.x, fieldMapper, doneMapper)})"
    is Expr.Ite -> "(ite ${exprToSmt(e.c, fieldMapper, doneMapper)} ${exprToSmt(e.t, fieldMapper, doneMapper)} ${exprToSmt(e.e, fieldMapper, doneMapper)})"
}

private fun smtType(type: Type): String = when (type) {
    is Type.BoolType -> "Bool"
    is Type.IntType -> "Int"
    is Type.SetType -> "Int"
}

private fun collectFields(expr: Expr): Set<FieldRef> = when (expr) {
    is Expr.Const.IntVal, is Expr.Const.BoolVal -> emptySet()
    is Expr.Const.Hidden -> collectFields(expr.inner)
    Expr.Const.Opaque -> emptySet()
    Expr.Const.Quit -> emptySet()
    is Expr.Field -> setOf(expr.field)
    is Expr.IsDefined -> setOf(expr.field)
    is Expr.Add -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Sub -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Mul -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Div -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Mod -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Neg -> collectFields(expr.x)
    is Expr.Eq -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Ne -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Lt -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Le -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Gt -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Ge -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.And -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Or -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Not -> collectFields(expr.x)
    is Expr.Ite -> collectFields(expr.c) + collectFields(expr.t) + collectFields(expr.e)
}

private fun fieldName(field: FieldRef): String = "${field.owner}_${field.param}"

private fun doneFieldName(field: FieldRef): String = "${fieldName(field)}_done"

private fun actionDoneName(id: ActionId): String = "action_${id.first}_${id.second}_done"

private fun outcomeName(role: RoleId): String = "${role}_outcome"

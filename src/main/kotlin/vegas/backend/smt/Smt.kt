package vegas.backend.smt

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.ActionGameIR
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.Type
import vegas.ir.dag

fun generateSMT(ir: ActionGameIR): String {
    val sb = StringBuilder()
    val dag = ir.dag

    val paramTypes: Map<FieldRef, Type> = dag.metas
        .flatMap { meta -> meta.spec.params.map { param -> FieldRef(meta.struct.role, param.name) to param.type } }
        .toMap()

    val referencedFields = mutableSetOf<FieldRef>()
    dag.metas.forEach { meta -> referencedFields += collectFields(meta.spec.guardExpr) }
    ir.payoffs.values.forEach { expr -> referencedFields += collectFields(expr) }

    val fieldTypes: Map<FieldRef, Type> = referencedFields.associateWith { field ->
        paramTypes[field] ?: Type.IntType
    }

    fieldTypes.forEach { (field, type) ->
        sb.appendLine("(declare-const ${fieldName(field)} ${smtType(type)})")
        sb.appendLine("(declare-const ${doneFieldName(field)} Bool)")
        appendDomainConstraint(sb, field, type)
        sb.appendLine()
    }

    dag.actions.sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name }).forEach { id ->
        sb.appendLine("(declare-const ${actionDoneName(id)} Bool)")
        val prereq = dag.prerequisitesOf(id).map { actionDoneName(it) }
        val guard = dag.spec(id).guardExpr
        val guardExpr = exprToSmt(guard)
        val prereqExpr = prereq.fold("true") { acc, name -> "(and $acc $name)" }
        sb.appendLine("(assert (=> ${actionDoneName(id)} (and $prereqExpr $guardExpr)))")
        dag.struct(id).writes.forEach { field ->
            sb.appendLine("(assert (=> ${actionDoneName(id)} ${doneFieldName(field)}))")
        }
        sb.appendLine()
    }

    ir.payoffs.forEach { (role, expr) ->
        sb.appendLine("(declare-const ${outcomeName(role)} Int)")
        sb.appendLine("(assert (= ${outcomeName(role)} ${exprToSmt(expr)}))")
        sb.appendLine()
    }

    sb.appendLine("(check-sat)")
    sb.appendLine("(get-model)")

    return sb.toString()
}

private fun appendDomainConstraint(sb: StringBuilder, field: FieldRef, type: Type) {
    when (type) {
        is Type.SetType -> {
            if (type.values.isNotEmpty()) {
                val clauses = type.values.sorted().joinToString(" ") { v -> "(= ${fieldName(field)} $v)" }
                sb.appendLine("(assert (or $clauses))")
            }
        }

        is Type.IntType, is Type.BoolType -> {}
    }
}

private fun exprToSmt(e: Expr): String = when (e) {
    is Expr.IntVal -> "${e.v}"
    is Expr.BoolVal -> "${e.v}"
    is Expr.Field -> fieldName(e.field)
    is Expr.IsDefined -> doneFieldName(e.field)
    is Expr.Add -> "(+ ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Sub -> "(- ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Mul -> "(* ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Div -> "(div ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Neg -> "(- ${exprToSmt(e.x)})"
    is Expr.Eq -> "(= ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Ne -> "(not (= ${exprToSmt(e.l)} ${exprToSmt(e.r)}))"
    is Expr.Lt -> "(< ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Le -> "(<= ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Gt -> "(> ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Ge -> "(>= ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.And -> "(and ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Or -> "(or ${exprToSmt(e.l)} ${exprToSmt(e.r)})"
    is Expr.Not -> "(not ${exprToSmt(e.x)})"
    is Expr.Ite -> "(ite ${exprToSmt(e.c)} ${exprToSmt(e.t)} ${exprToSmt(e.e)})"
}

private fun smtType(type: Type): String = when (type) {
    is Type.BoolType -> "Bool"
    is Type.IntType -> "Int"
    is Type.SetType -> "Int"
}

private fun collectFields(expr: Expr): Set<FieldRef> = when (expr) {
    is Expr.IntVal, is Expr.BoolVal -> emptySet()
    is Expr.Field -> setOf(expr.field)
    is Expr.IsDefined -> setOf(expr.field)
    is Expr.Add -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Sub -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Mul -> collectFields(expr.l) + collectFields(expr.r)
    is Expr.Div -> collectFields(expr.l) + collectFields(expr.r)
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

private fun fieldName(field: FieldRef): String = "${field.role}_${field.param}"

private fun doneFieldName(field: FieldRef): String = "${fieldName(field)}_done"

private fun actionDoneName(id: ActionId): String = "action_${id.first}_${id.second}_done"

private fun outcomeName(role: RoleId): String = "${role}_outcome"

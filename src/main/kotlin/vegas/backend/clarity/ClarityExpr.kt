package vegas.backend.clarity

import vegas.FieldRef
import vegas.ir.Expr
import vegas.ir.Expr.*

internal fun translateExpr(e: Expr, fieldToActionIds: (FieldRef) -> List<Int>, localParams: Map<FieldRef, String> = emptyMap()): String = when (e) {
    // Literals
    is Const.IntVal -> "${e.v}" // Clarity int is signed 128
    is Const.BoolVal -> "${e.v}"
    is Const.Hidden -> error("Hidden value in runtime expression")
    Const.Opaque -> error("Opaque value in runtime expression")
    Const.Quit -> error("Quit value in runtime expression")

    // Field Access
    is Field -> localParams[e.field] ?: "(var-get var-${kebab(e.field.owner.name)}-${kebab(e.field.param.name)})"

    // Meta-ops
    is IsDefined -> {
        val ids = fieldToActionIds(e.field)
        if (ids.isEmpty()) "false"
        else if (ids.size == 1) "(is-done u${ids[0]})"
        else "(or ${ids.joinToString(" ") { "(is-done u$it)" }})"
    }

    // Arithmetic
    is Add -> "(+ ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Sub -> "(- ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Mul -> "(* ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Div -> "(/ ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Mod -> "(mod ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Neg -> "(- 0 ${translateExpr(e.x, fieldToActionIds, localParams)})" // 0 - x for negation

    // Comparisons
    is Eq -> "(is-eq ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Ne -> "(not (is-eq ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)}))"
    is Lt -> "(< ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Le -> "(<= ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Gt -> "(> ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Ge -> "(>= ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"

    // Boolean
    is And -> "(and ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Or -> "(or ${translateExpr(e.l, fieldToActionIds, localParams)} ${translateExpr(e.r, fieldToActionIds, localParams)})"
    is Not -> "(not ${translateExpr(e.x, fieldToActionIds, localParams)})"
    is Ite -> "(if ${translateExpr(e.c, fieldToActionIds, localParams)} ${translateExpr(e.t, fieldToActionIds, localParams)} ${translateExpr(e.e, fieldToActionIds, localParams)})"
}

private fun kebab(s: String): String = s.fold(StringBuilder()) { acc, c ->
    if (c.isUpperCase()) {
        if (acc.isNotEmpty()) acc.append('-')
        acc.append(c.lowercaseChar())
    } else {
        acc.append(c)
    }
}.toString()

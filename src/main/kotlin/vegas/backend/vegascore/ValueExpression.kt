package vegas.backend.vegascore

import vegas.FieldRef
import vegas.ir.Expr
import vegas.ir.Type

/** A reference to a core variable and the representation it has in the current context. */
internal data class ValueRef(val code: String, val type: Type, val published: Boolean, val guardPublication: Boolean = false)

private enum class ValueKind { BOOL, INT }

/** Expressions preserve the distinction between a boolean, an integer, and a failed publication. */
private data class ValueCode(
    val kind: ValueKind,
    val code: String,
    val result: Boolean = false,
    val mayFail: Boolean = false,
) {
    fun asResult(): String = if (result) code else "(.success $code)"
    fun isDefined(): String = "(.isSuccess ${asResult()})"
    fun value(fallback: String): String = if (result) "(.getResultD $code $fallback)" else code

    fun bool(): String = when (kind) {
        ValueKind.BOOL -> value("(.constBool false)")
        ValueKind.INT -> "(.notBool (.eq ${value("(.constInt 0)")} (.constInt 0)))"
    }

    fun int(): String {
        if (mayFail) throw UnsupportedCoreElaboration("numeric use of a possibly failed publication")
        return when (kind) {
            ValueKind.INT -> value("(.constInt 0)")
            ValueKind.BOOL -> "(.ite ${bool()} (.constInt 1) (.constInt 0))"
        }
    }
}

/**
 * Elaborate the IR value expression. The input is the IR evaluator's ordinary value domain.
 * Numeric operations and payouts require values on all reached branches. Public failure
 * tests use publication results.
 */
internal class ValueExpression(private val read: (FieldRef) -> ValueRef) {
    fun guard(expr: Expr, subject: FieldRef): String = emit(expr, Facts(guardSubject = subject)).bool()
    fun payout(expr: Expr): String = emit(expr, Facts()).int()

    private fun field(field: FieldRef, facts: Facts): ValueCode {
        val (code, type, published) = read(field)
        val mayFail = published && field !in facts.defined
        return when (type) {
            Type.BoolType -> ValueCode(ValueKind.BOOL, code, published, mayFail)
            Type.IntType -> ValueCode(ValueKind.INT, code, published, mayFail)
            is Type.RangeType -> {
                val base = if (published)
                    "(.getResultD $code (.constRange (lo := ${type.min}) (len := ${type.max.toLong() - type.min}) (Subtype.mk (${type.min}) (by decide))))"
                else code
                val value = "(.rangeToInt $base)"
                val lifted = if (published) "(.ite (.isSuccess $code) (.success $value) .failure)" else value
                ValueCode(ValueKind.INT, lifted, published, mayFail)
            }
        }
    }

    private fun bool(code: String) = ValueCode(ValueKind.BOOL, code)
    private fun int(code: String) = ValueCode(ValueKind.INT, code)

    private fun arithmetic(op: String, left: Expr, right: Expr, facts: Facts): ValueCode {
        val lhs = emit(left, facts).int()
        val rhs = emit(right, facts).int()
        if ((op == "div" || op == "mod") && !facts.provesNonzero(right)) {
            throw UnsupportedCoreElaboration("could not prove that the divisor is nonzero")
        }
        return int("(.signedInt .$op $lhs $rhs)")
    }

    private fun less(left: Expr, right: Expr, facts: Facts): String =
        "(.ltInt ${emit(left, facts).int()} ${emit(right, facts).int()})"

    private fun eq(left: Expr, right: Expr, facts: Facts): String {
        val lhs = emit(left, facts)
        val rhs = emit(right, facts)
        return if (lhs.kind == rhs.kind)
            "(.eq ${lhs.asResult()} ${rhs.asResult()})"
        else
            "(.andBool (.notBool ${lhs.isDefined()}) (.notBool ${rhs.isDefined()}))"
    }

    private fun ite(conditional: Expr.Ite, facts: Facts): ValueCode {
        val condition = emit(conditional.c, facts).bool()
        val yes = emit(conditional.t, facts.with(conditional.c, true))
        val no = emit(conditional.e, facts.with(conditional.c, false))
        if (yes.kind != no.kind) {
            throw UnsupportedCoreElaboration("conditional branches have different value types")
        }
        return if (yes.result || no.result)
            ValueCode(yes.kind, "(.ite $condition ${yes.asResult()} ${no.asResult()})",
                result = true, mayFail = yes.mayFail || no.mayFail)
        else
            ValueCode(yes.kind, "(.ite $condition ${yes.code} ${no.code})")
    }

    private fun defined(field: FieldRef, facts: Facts): ValueCode {
        val ref = read(field)
        if (facts.guardSubject != null && field != facts.guardSubject && ref.guardPublication) {
            throw UnsupportedCoreElaboration("guard tests whether another field $field was published")
        }
        val result = if (ref.published && facts.guardSubject == null) ref.code else "(.success ${ref.code})"
        return bool("(.isSuccess $result)")
    }

    private fun emit(expr: Expr, facts: Facts): ValueCode = when (expr) {
        is Expr.Const.IntVal -> int("(.constInt (${expr.v}))")
        is Expr.Const.BoolVal -> bool("(.constBool ${expr.v})")
        is Expr.Field -> field(expr.field, facts)
        is Expr.IsDefined -> defined(expr.field, facts)
        is Expr.Add -> arithmetic("add", expr.l, expr.r, facts)
        is Expr.Sub -> arithmetic("sub", expr.l, expr.r, facts)
        is Expr.Mul -> arithmetic("mul", expr.l, expr.r, facts)
        is Expr.Div -> arithmetic("div", expr.l, expr.r, facts)
        is Expr.Mod -> arithmetic("mod", expr.l, expr.r, facts)
        is Expr.Neg -> arithmetic("sub", Expr.Const.IntVal(0), expr.x, facts)
        is Expr.Eq -> bool(eq(expr.l, expr.r, facts))
        is Expr.Ne -> bool("(.notBool ${eq(expr.l, expr.r, facts)})")
        is Expr.Lt -> bool(less(expr.l, expr.r, facts))
        is Expr.Le -> bool("(.notBool ${less(expr.r, expr.l, facts)})")
        is Expr.Gt -> bool(less(expr.r, expr.l, facts))
        is Expr.Ge -> bool("(.notBool ${less(expr.l, expr.r, facts)})")
        is Expr.And -> bool("(.andBool ${emit(expr.l, facts).bool()} ${emit(expr.r, facts.with(expr.l, true)).bool()})")
        is Expr.Or -> bool("(.ite ${emit(expr.l, facts).bool()} (.constBool true) ${emit(expr.r, facts.with(expr.l, false)).bool()})")
        is Expr.Not -> bool("(.notBool ${emit(expr.x, facts).bool()})")
        is Expr.Ite -> ite(expr, facts)
        is Expr.Const.Hidden, Expr.Const.Opaque, Expr.Const.Quit ->
            throw UnsupportedCoreElaboration("unsupported literal in value expression: $expr")
    }

    private data class Facts(
        val guardSubject: FieldRef? = null,
        val defined: Set<FieldRef> = emptySet(),
        val nonzero: Set<Expr> = emptySet(),
        val conditions: Map<Expr, Boolean> = emptyMap(),
    ) {
        /** Keep facts common to every short-circuit path to the given boolean result. */
        fun with(condition: Expr, value: Boolean): Facts {
            val known = copy(conditions = conditions + (condition to value))
            return when (condition) {
                is Expr.IsDefined -> if (value) known.copy(defined = defined + condition.field) else known
                is Expr.Field -> if (value) known.copy(defined = defined + condition.field) else known
                is Expr.Not -> known.with(condition.x, !value)
                is Expr.And -> if (value)
                    known.with(condition.l, true).with(condition.r, true)
                else
                    known.intersect(known.with(condition.l, false), known.with(condition.l, true).with(condition.r, false))
                is Expr.Or -> if (value)
                    known.intersect(known.with(condition.l, true), known.with(condition.l, false).with(condition.r, true))
                else
                    known.with(condition.l, false).with(condition.r, false)
                is Expr.Gt ->
                    if (value && condition.r == Expr.Const.IntVal(0)) known.copy(nonzero = nonzero + condition.l) else known
                is Expr.Lt ->
                    if (value && condition.r == Expr.Const.IntVal(0)) known.copy(nonzero = nonzero + condition.l) else known
                else -> known
            }
        }

        private fun intersect(left: Facts, right: Facts): Facts =
            copy(
                defined = left.defined intersect right.defined,
                nonzero = left.nonzero intersect right.nonzero,
                conditions = left.conditions.filter { (expr, value) -> right.conditions[expr] == value },
            )

        fun provesNonzero(expr: Expr): Boolean = expr in nonzero || when (expr) {
            is Expr.Ite -> when (conditions[expr.c]) {
                true -> with(expr.c, true).provesNonzero(expr.t)
                false -> with(expr.c, false).provesNonzero(expr.e)
                null -> with(expr.c, true).provesNonzero(expr.t) && with(expr.c, false).provesNonzero(expr.e)
            }
            else -> bounds(expr)?.let { 0 !in it } ?: false
        }

        /** Bounds for sums of conditional counts, checked for overflow before use. */
        private fun bounds(expr: Expr): IntRange? {
            return when (expr) {
                is Expr.Const.IntVal -> expr.v..expr.v
                is Expr.Const.BoolVal -> if (expr.v) 1..1 else 0..0
                is Expr.Ite -> when (conditions[expr.c]) {
                    true -> with(expr.c, true).bounds(expr.t)
                    false -> with(expr.c, false).bounds(expr.e)
                    null -> {
                        val yes = with(expr.c, true).bounds(expr.t) ?: return null
                        val no = with(expr.c, false).bounds(expr.e) ?: return null
                        minOf(yes.first, no.first)..maxOf(yes.last, no.last)
                    }
                }
                is Expr.Add -> {
                    val left = bounds(expr.l) ?: return null
                    val right = bounds(expr.r) ?: return null
                    val min = left.first.toLong() + right.first
                    val max = left.last.toLong() + right.last
                    if (min >= Int.MIN_VALUE && max <= Int.MAX_VALUE) min.toInt()..max.toInt() else null
                }
                else -> null
            }
        }
    }
}

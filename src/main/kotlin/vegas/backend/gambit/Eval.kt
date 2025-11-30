package vegas.backend.gambit

import vegas.FieldRef
import vegas.ir.Expr

internal sealed class IrVal {
    data class IntVal(val v: Int) : IrVal()
    data class BoolVal(val v: Boolean) : IrVal()
    data class Hidden(val inner: IrVal) : IrVal()   // value chosen but not visible to others
    object Opaque : IrVal()  // commitment made but value hidden from observer
    object Quit : IrVal()  // bail/abandonment

    fun toOutcome(): IntVal = when (this) {
        is IntVal -> IntVal(v)
        is BoolVal -> IntVal(if (v) 1 else 0)
        is Hidden, Opaque, Quit -> error("Terminal payoff references undefined/hidden value")
    }

    fun asBool(): Boolean = when (this) {
        is BoolVal -> v
        is IntVal -> v != 0
        is Hidden, Opaque, Quit -> false
    }

    fun asInt(): Int = when (this) {
        is IntVal -> v
        is BoolVal -> if (v) 1 else 0
        is Hidden, Opaque, Quit -> error("Expected int, got $this")
    }
}

internal fun eval(readField: (FieldRef)-> IrVal, e: Expr): IrVal {
    fun eq(a: IrVal, b: IrVal): Boolean = when {
        a is IrVal.IntVal && b is IrVal.IntVal -> a.v == b.v
        a is IrVal.BoolVal && b is IrVal.BoolVal -> a.v == b.v
        a is IrVal.Quit && b is IrVal.Quit -> true
        else -> false
    }

    fun eval0(x: Expr): IrVal = when (x) {
        is Expr.Const.IntVal -> IrVal.IntVal(x.v)
        is Expr.Const.BoolVal -> IrVal.BoolVal(x.v)
        is Expr.Field -> readField(x.field)
        is Expr.IsDefined -> {
            val v = readField(x.field)
            IrVal.BoolVal(v !is IrVal.Quit && v !is IrVal.Hidden && v !is IrVal.Opaque)
        }

        // arithmetic
        is Expr.Add -> IrVal.IntVal(eval0(x.l).asInt() + eval0(x.r).asInt())
        is Expr.Sub -> IrVal.IntVal(eval0(x.l).asInt() - eval0(x.r).asInt())
        is Expr.Mul -> IrVal.IntVal(eval0(x.l).asInt() * eval0(x.r).asInt())
        is Expr.Div -> IrVal.IntVal(eval0(x.l).asInt() / eval0(x.r).asInt())
        is Expr.Neg -> IrVal.IntVal(-eval0(x.x).asInt())

        // comparisons
        is Expr.Eq -> IrVal.BoolVal(eq(eval0(x.l), eval0(x.r)))
        is Expr.Ne -> IrVal.BoolVal(!eq(eval0(x.l), eval0(x.r)))
        is Expr.Lt -> IrVal.BoolVal(eval0(x.l).asInt() < eval0(x.r).asInt())
        is Expr.Le -> IrVal.BoolVal(eval0(x.l).asInt() <= eval0(x.r).asInt())
        is Expr.Gt -> IrVal.BoolVal(eval0(x.l).asInt() > eval0(x.r).asInt())
        is Expr.Ge -> IrVal.BoolVal(eval0(x.l).asInt() >= eval0(x.r).asInt())

        // boolean
        is Expr.And -> IrVal.BoolVal(eval0(x.l).asBool() && eval0(x.r).asBool())
        is Expr.Or -> IrVal.BoolVal(eval0(x.l).asBool() || eval0(x.r).asBool())
        is Expr.Not -> IrVal.BoolVal(!eval0(x.x).asBool())
        is Expr.Ite -> if (eval0(x.c).asBool()) eval0(x.t) else eval0(x.e)
    }

    return eval0(e)
}

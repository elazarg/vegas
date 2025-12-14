package vegas.semantics

import vegas.FieldRef
import vegas.ir.Expr
import vegas.ir.asBool
import vegas.ir.asInt
import vegas.ir.Expr.Const.*

internal fun eval(readField: (FieldRef)-> Expr.Const, e: Expr): Expr.Const {
    fun eq(a: Expr.Const, b: Expr.Const): Boolean = when {
        a is IntVal && b is IntVal -> a.v == b.v
        a is BoolVal && b is BoolVal -> a.v == b.v
        a is Quit && b is Quit -> true
        else -> false
    }

    fun eval0(x: Expr): Expr.Const = when (x) {
        is IntVal -> x
        is BoolVal -> x
        is Hidden -> x
        is Opaque -> x
        is Quit -> x
        is Expr.Field -> readField(x.field)
        is Expr.IsDefined -> {
            val v = readField(x.field)
            BoolVal(v !is Quit)
        }

        // arithmetic
        is Expr.Add -> IntVal(eval0(x.l).asInt() + eval0(x.r).asInt())
        is Expr.Sub -> IntVal(eval0(x.l).asInt() - eval0(x.r).asInt())
        is Expr.Mul -> IntVal(eval0(x.l).asInt() * eval0(x.r).asInt())
        is Expr.Div -> IntVal(eval0(x.l).asInt() / eval0(x.r).asInt())
        is Expr.Mod -> IntVal(eval0(x.l).asInt() % eval0(x.r).asInt())
        is Expr.Neg -> IntVal(-eval0(x.x).asInt())

        // comparisons
        is Expr.Eq -> BoolVal(eq(eval0(x.l), eval0(x.r)))
        is Expr.Ne -> BoolVal(!eq(eval0(x.l), eval0(x.r)))
        is Expr.Lt -> BoolVal(eval0(x.l).asInt() < eval0(x.r).asInt())
        is Expr.Le -> BoolVal(eval0(x.l).asInt() <= eval0(x.r).asInt())
        is Expr.Gt -> BoolVal(eval0(x.l).asInt() > eval0(x.r).asInt())
        is Expr.Ge -> BoolVal(eval0(x.l).asInt() >= eval0(x.r).asInt())

        // boolean
        is Expr.And -> BoolVal(eval0(x.l).asBool() && eval0(x.r).asBool())
        is Expr.Or -> BoolVal(eval0(x.l).asBool() || eval0(x.r).asBool())
        is Expr.Not -> BoolVal(!eval0(x.x).asBool())
        is Expr.Ite -> if (eval0(x.c).asBool()) eval0(x.t) else eval0(x.e)
    }

    return eval0(e)
}

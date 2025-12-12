package vegas.semantics

import vegas.Env
import vegas.frontend.Exp
import vegas.frontend.Exp.*
import vegas.frontend.Exp.Const.*

fun eval(exp: Exp, env: Env<Const>): Const {
    fun rec(e: Exp): Const = when (e) {
        is Call -> when (e.target.id.name) {
            "alldiff" -> Bool(e.args.map { rec(it) }.distinct().size == e.args.size)
            else -> throw NotImplementedError("Unknown function: ${e.target.id.name}")
        }

        is UnOp -> {
            val v = rec(e.operand)
            when (e.op) {
                "-" -> Num(-((v as Num).n))
                "!" -> Bool(!(v as Bool).truth)
                "isUndefined" -> Bool(v == UNDEFINED)
                "isDefined" -> Bool(v != UNDEFINED)
                else -> throw AssertionError("Unknown unary op ${e.op}")
            }
        }

        is BinOp -> {
            val l = rec(e.left)
            val r = rec(e.right)
            when (e.op) {
                "==" -> Bool(l == r)
                "!=" -> Bool(l != r)
                "<->" -> Bool(l == r)
                "<-!->" -> Bool(l != r)
                "+", "-", "*", "/", "%", "<", "<=", ">", ">=" ->
                    if (l is Num && r is Num) when (e.op) {
                        "+" -> Num(l.n + r.n)
                        "-" -> Num(l.n - r.n)
                        "*" -> Num(l.n * r.n)
                        "/" -> Num(l.n / r.n)
                        "%" -> Num(l.n % r.n)
                        "<" -> Bool(l.n < r.n)
                        "<=" -> Bool(l.n <= r.n)
                        ">" -> Bool(l.n > r.n)
                        ">=" -> Bool(l.n >= r.n)
                        else -> throw AssertionError()
                    } else throw AssertionError("$l ${e.op} $r")
                "&&", "||" ->
                    if (l is Bool && r is Bool) when (e.op) {
                        "&&" -> Bool(l.truth && r.truth)
                        "||" -> Bool(l.truth || r.truth)
                        else -> throw AssertionError()
                    } else throw AssertionError("$l ${e.op} $r")
                else -> throw AssertionError("Unknown binary op ${e.op}")
            }
        }

        is Var -> env.getValue(e.id)
        is Field -> env.getValue(e.fieldRef)

        is Cond -> when (val c = rec(e.cond)) {
            is Bool -> if (c.truth) rec(e.ifTrue) else rec(e.ifFalse)
            else -> throw AssertionError("Condition not boolean: $c")
        }

        is Let -> {
            val v = rec(e.init)
            eval(e.exp, env + (e.dec.v.id to v))
        }

        is Num, is Bool, is Hidden, is Address -> e
        UNDEFINED -> UNDEFINED
    }

    return rec(exp)
}

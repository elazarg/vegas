package vegas.ir

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef

// Expression are mostly straightforward
sealed class Expr {
    // literals
    sealed class Const : Expr() {
        data class IntVal(val v: Int) : Const()
        data class BoolVal(val v: Boolean) : Const()

        // Information and game-specific decisions
        data class Hidden(val inner: Const) : Const()   // value chosen but not visible to others
        object Opaque : Const()  // commitment made but value hidden from observer
        object Quit : Const()  // abandonment
    }

    data class Field(val field: FieldRef) : Expr()

    data class IsDefined(val field: FieldRef) : Expr()

    // arithmetic
    data class Add(val l: Expr, val r: Expr) : Expr()
    data class Sub(val l: Expr, val r: Expr) : Expr()
    data class Mul(val l: Expr, val r: Expr) : Expr()
    data class Div(val l: Expr, val r: Expr) : Expr()
    data class Mod(val l: Expr, val r: Expr) : Expr()
    data class Neg(val x: Expr) : Expr()

    // comparisons
    data class Eq(val l: Expr, val r: Expr) : Expr()
    data class Ne(val l: Expr, val r: Expr) : Expr()
    data class Lt(val l: Expr, val r: Expr) : Expr()
    data class Le(val l: Expr, val r: Expr) : Expr()
    data class Gt(val l: Expr, val r: Expr) : Expr()
    data class Ge(val l: Expr, val r: Expr) : Expr()

    // boolean
    data class And(val l: Expr, val r: Expr) : Expr()
    data class Or (val l: Expr, val r: Expr) : Expr()
    data class Not(val x: Expr) : Expr()
    data class Ite(val c: Expr, val t: Expr, val e: Expr) : Expr()
}


fun Expr.Const.toOutcome(): Expr.Const.IntVal  = when (this) {
    is Expr.Const.IntVal -> Expr.Const.IntVal(v)
    is Expr.Const.BoolVal -> Expr.Const.IntVal(if (v) 1 else 0)
    else -> error("Terminal payoff references undefined/hidden value")
}

fun Expr.Const.asBool(): Boolean = when (this) {
    is Expr.Const.BoolVal -> v
    is Expr.Const.IntVal -> v != 0
    else -> false
}

fun Expr.Const.asInt(): Int = when (this) {
    is Expr.Const.IntVal -> v
    is Expr.Const.BoolVal -> if (v) 1 else 0
    else-> error("Expected int, got $this")
}

/**
 * Requirements specify when an action can execute.
 *
 * after: Control dependencies (must-happen-before). Forms DAG.
 * sees: Data dependencies (which fields this action's condition reads).
 *       WF condition: Fields in condition must appear in sees.
 * condition: Logical guard enabling action.
 *
 * UNDEFINED SEMANTICS:
 * If condition references undefined field (action not yet complete),
 * condition evaluates to false (action not enabled).
 * All backends implement via "done flags": <action>_<param>_done.
 */
data class Requirement(
    val captures: Set<FieldRef>,    // Fields this guard MAY read (must be from earlier phases)
//    val deferred: Set<FieldRef>,    // Captures that are hidden (deferred)
    val condition: Expr             // boolean; see "Guard scheduling"
)

data class Join(
    val deposit: Expr.Const.IntVal,
)

sealed class Type {
    object IntType : Type()
    object BoolType : Type()
    data class SetType(val values: Set<Int>) : Type()
}

/**
 * A Parameter represents data provided when executing an action.
 *
 * "visible" means reveal if "invisible" was already declared. A second "invisible" might be "reconsidered", or malformed.
 */
data class Parameter(
    val name: VarId,
    val type: Type,
    val visible: Boolean,
)

/**
 * A Signature is something a role does: join, submit data, commit or reveal hidden info.
 */
data class Signature(
    val join: Join?,              // non-null if this is the role's "join" step
    val parameters: List<Parameter>,
    val requires: Requirement      // guard for this action (snapshot semantics)
)

/**
 * A GameIR describes a multi-party interaction where roles perform actions
 * that may depend on each other, leading to payoffs for each role.
 */
data class GameIR(
    val name: String,
    val roles: Set<RoleId>,
    val chanceRoles: Set<RoleId>,
    val dag: ActionDag,
    val payoffs: Map<RoleId, Expr>
)

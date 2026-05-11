package vegas.ir

import vegas.Rational
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
 * Guard: the precondition gating a node's execution.
 *
 * scope: Fields this guard MAY read. Must be DAG predecessors.
 * expr:  Boolean expression; the node fires only when it evaluates true.
 *
 * Aligned with VegasCore's per-node guard predicate `R`.
 */
data class Guard(
    val scope: Set<FieldRef>,
    val expr: Expr,
)

data class Join(
    val deposit: Expr.Const.IntVal,
)

/**
 * A finite probability distribution over Expr.Const values, normalized.
 *
 * Used by Sample nodes (chance / RNG) to declare the underlying randomness.
 * Backends that compute posterior probabilities (Gambit, MAID, PRISM) must
 * renormalize over the guard-surviving support per reachable context; the
 * Dist itself is the *prior* declared at the source.
 *
 * Invariants:
 *  - support is non-empty
 *  - keys are distinct
 *  - all weights are strictly positive
 *  - weights sum to 1
 */
data class Dist(val support: List<Pair<Expr.Const, Rational>>) {
    init {
        require(support.isNotEmpty()) { "Dist support must be non-empty" }
        require(support.distinctBy { it.first }.size == support.size) {
            "Dist keys must be distinct: $support"
        }
        require(support.all { it.second.numerator > 0 }) {
            "Dist weights must be strictly positive: $support"
        }
        val sum = support.map { it.second }.reduce { a, b -> a + b }
        require(sum == Rational(1)) { "Dist weights must sum to 1, got $sum: $support" }
    }

    val values: List<Expr.Const> get() = support.map { it.first }

    fun weight(v: Expr.Const): Rational? =
        support.firstOrNull { it.first == v }?.second

    companion object {
        fun uniform(values: List<Expr.Const>): Dist {
            require(values.isNotEmpty()) { "Cannot build uniform Dist over empty support" }
            val w = Rational(1, values.size)
            return Dist(values.map { it to w })
        }
    }
}

/**
 * Where the randomness for a Sample node physically comes from.
 *
 * Each source carries a distinct threat model (who can bias the draw).
 * Stage 1 supports only RoleSubmit, which is the legacy "random Role()"
 * semantics. EVM-native sources (prevrandao, vrf, drand, commit_reveal
 * aggregation) are reserved for later stages.
 */
sealed class EntropySource {
    /**
     * A designated role submits the value. Trust assumption: that role.
     * This is the back-compat representation of today's "random Role()".
     */
    data class RoleSubmit(val role: RoleId) : EntropySource()
}

/**
 * Per-node classification of a Sample (chance) node.
 *
 * @property dist   Declared prior distribution at the source. May be null
 *                  when no explicit distribution is yet declared on the
 *                  surface (back-compat path): backends then fall back to
 *                  their legacy uniform-over-surviving-moves behavior.
 * @property source Physical entropy source. Stage 1: always RoleSubmit.
 */
data class SampleSpec(
    val dist: Dist?,
    val source: EntropySource,
)

sealed class Type {
    object IntType : Type()
    object BoolType : Type()
    data class RangeType(val min: Int, val max: Int) : Type()
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
    val guard: Guard,             // precondition for this action (snapshot semantics)
)

/**
 * A GameIR describes a multi-party interaction where roles perform actions
 * that may depend on each other, leading to payoffs for each role.
 */
data class GameIR(
    val name: String,
    val roles: Set<RoleId>,
    val chanceRoles: Set<RoleId>,
    val dag: EventGraph,
    val payoffs: Map<RoleId, Expr>
)

package vegas.backend.solidity

/**
* DSL helpers for building Solidity AST.
* Makes code more readable and less verbose.
*/
// ===== Literals =====

fun int(value: Int) = SolExpr.IntLit(value)
fun bool(value: Boolean) = SolExpr.BoolLit(value)

// ===== Variables =====

fun v(name: String) = SolExpr.Var(name)

// ===== Member Access =====

infix fun SolExpr.dot(member: String) = SolExpr.Member(this, member)
operator fun SolExpr.get(index: SolExpr) = SolExpr.Index(this, index)

// Convenience for common patterns
fun index(base: String, idx: SolExpr) = SolExpr.Index(v(base), idx)

// ===== Comparisons =====

infix fun SolExpr.eq(other: SolExpr) = SolExpr.Eq(this, other)
infix fun SolExpr.ne(other: SolExpr) = SolExpr.Ne(this, other)
infix fun SolExpr.lt(other: SolExpr) = SolExpr.Lt(this, other)
infix fun SolExpr.le(other: SolExpr) = SolExpr.Le(this, other)
infix fun SolExpr.gt(other: SolExpr) = SolExpr.Gt(this, other)
infix fun SolExpr.ge(other: SolExpr) = SolExpr.Ge(this, other)

// ===== Boolean Logic =====

infix fun SolExpr.and(other: SolExpr) = SolExpr.And(this, other)
infix fun SolExpr.or(other: SolExpr) = SolExpr.Or(this, other)
fun not(expr: SolExpr) = SolExpr.Not(expr)

// ===== Arithmetic =====
fun neg(expr: SolExpr) = SolExpr.Neg(expr)
operator fun SolExpr.plus(other: SolExpr) = SolExpr.Add(this, other)
operator fun SolExpr.minus(other: SolExpr) = SolExpr.Sub(this, other)
operator fun SolExpr.times(other: SolExpr) = SolExpr.Mul(this, other)
operator fun SolExpr.div(other: SolExpr) = SolExpr.Div(this, other)
operator fun SolExpr.rem(other: SolExpr) = SolExpr.Mod(this, other)
operator fun SolExpr.unaryMinus() = SolExpr.Neg(this)


// ===== Casts =====

fun cast(type: SolType, expr: SolExpr) = SolExpr.Cast(type, expr)
fun toBytes32(expr: SolExpr) = SolExpr.Cast(SolType.Bytes32, expr)

// ===== Modifiers =====

fun depends(actionId: Int) = ModifierCall("depends", listOf(int(actionId)))
fun notDone(actionId: Int) = ModifierCall("notDone", listOf(int(actionId)))
fun atFinalPhase() = ModifierCall("at_final_phase", emptyList())

// ===== Built-ins =====

val msgSender = SolExpr.BuiltIn.MsgSender
val msgValue = SolExpr.BuiltIn.MsgValue
val blockTimestamp = SolExpr.BuiltIn.BlockTimestamp

// ===== Solidity-Specific =====

fun enumVal(enumType: String, value: String) = SolExpr.EnumValue(enumType, value)
fun keccak256(data: SolExpr) = SolExpr.Keccak256(data)
fun abiEncodePacked(vararg args: SolExpr) = SolExpr.AbiEncodePacked(args.toList())

// ===== Statements =====

fun require(condition: SolExpr, message: String) =
    Statement.Require(condition, message)

fun assign(lhs: SolExpr, rhs: SolExpr) =
    Statement.Assign(lhs, rhs)

// ===== Common Patterns =====
/**
 * Common pattern: balanceOf[msg.sender] = msg.value
 */
fun setBalance() = assign(
    lhs = index(BALANCE_MAPPING, msgSender),
    rhs = msgValue
)

/**
 * Common pattern: require(msg.value == amount, "bad stake")
 */
fun requireDeposit(amount: Int) = require(
    msgValue eq int(amount),
    "bad stake"
)

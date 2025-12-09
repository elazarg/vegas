package vegas.backend.vyper

/**
 * DSL helpers for building Vyper AST.
 * Makes code more readable and less verbose.
 */

// ===== Literals =====

fun int(value: Int) = VyExpr.IntLit(value)
fun bool(value: Boolean) = VyExpr.BoolLit(value)
fun str(value: String) = VyExpr.StringLit(value)
fun bytes(value: String) = VyExpr.BytesLit(value)

// ===== Variables =====

fun v(name: String) = VyExpr.Var(name)
fun selfMember(member: String) = VyExpr.SelfMember(member)

// ===== Member Access =====

operator fun VyExpr.get(index: VyExpr) = VyExpr.Index(this, index)

fun selfIndex(base: String, idx: VyExpr) =
    VyExpr.Index(VyExpr.SelfMember(base), idx)

// ===== Comparisons =====

infix fun VyExpr.eq(other: VyExpr) = VyExpr.Eq(this, other)
infix fun VyExpr.ne(other: VyExpr) = VyExpr.Ne(this, other)
infix fun VyExpr.lt(other: VyExpr) = VyExpr.Lt(this, other)
infix fun VyExpr.le(other: VyExpr) = VyExpr.Le(this, other)
infix fun VyExpr.gt(other: VyExpr) = VyExpr.Gt(this, other)
infix fun VyExpr.ge(other: VyExpr) = VyExpr.Ge(this, other)

// ===== Boolean Logic =====

infix fun VyExpr.and(other: VyExpr) = VyExpr.And(this, other)
infix fun VyExpr.or(other: VyExpr) = VyExpr.Or(this, other)
fun not(expr: VyExpr) = VyExpr.Not(expr)

// ===== Arithmetic =====

fun neg(expr: VyExpr) = VyExpr.Neg(expr)
operator fun VyExpr.plus(other: VyExpr) = VyExpr.Add(this, other)
operator fun VyExpr.minus(other: VyExpr) = VyExpr.Sub(this, other)
operator fun VyExpr.times(other: VyExpr) = VyExpr.Mul(this, other)
operator fun VyExpr.div(other: VyExpr) = VyExpr.Div(this, other)
operator fun VyExpr.rem(other: VyExpr) = VyExpr.Mod(this, other)
operator fun VyExpr.unaryMinus() = VyExpr.Neg(this)

// ===== Built-ins =====

val msgSender = VyExpr.BuiltIn.MsgSender
val msgValue = VyExpr.BuiltIn.MsgValue
val blockTimestamp = VyExpr.BuiltIn.BlockTimestamp
val selfAddress = VyExpr.BuiltIn.SelfAddress
val bytes32Zero = VyExpr.BuiltIn.Bytes32Zero
val vyTrue = VyExpr.BuiltIn.True
val vyFalse = VyExpr.BuiltIn.False

// ===== Vyper-Specific =====

fun enumVal(enumType: String, value: String) = VyExpr.EnumValue(enumType, value)

fun vyKeccak256(data: VyExpr) = VyExpr.Keccak256(data)

fun abiEncode(vararg args: VyExpr, outputType: VyType) =
    VyExpr.AbiEncode(args.toList(), outputType)

fun convert(expr: VyExpr, type: VyType) = VyExpr.Convert(type, expr)

fun call(function: String, vararg args: VyExpr, kwargs: Map<String, VyExpr> = emptyMap()) =
    VyExpr.Call(function, args.toList(), kwargs)

fun rawCall(target: VyExpr, data: VyExpr, value: VyExpr? = null, maxOutsize: Int = 0, gas: Int? = null) =
    VyExpr.RawCall(target, data, value, maxOutsize, gas)

// ===== Statements =====

fun vyAssert(condition: VyExpr, message: String) =
    Statement.Assert(condition, message)

fun assign(lhs: VyExpr, rhs: VyExpr) =
    Statement.Assign(lhs, rhs)

fun varDecl(type: VyType, name: String, init: VyExpr? = null) =
    Statement.VarDecl(type, name, init)

fun exprStmt(expr: VyExpr) = Statement.ExprStmt(expr)

fun ret(value: VyExpr? = null) = Statement.Return(value)

fun vyIf(condition: VyExpr, thenBranch: List<Statement>, elseBranch: List<Statement> = emptyList()) =
    Statement.If(condition, thenBranch, elseBranch)

val pass = Statement.Pass

fun raw(code: String) = Statement.Raw(code)

// ===== Common Patterns =====

/**
 * Common pattern: self.balanceOf[msg.sender] = msg.value
 */
fun setBalance() = assign(
    lhs = selfIndex(BALANCE_MAPPING, msgSender),
    rhs = msgValue
)

/**
 * Common pattern: assert msg.value == amount, "bad stake"
 */
fun requireDeposit(amount: Int) = vyAssert(
    msgValue eq int(amount),
    "bad stake"
)

/**
 * Common pattern: self.role[msg.sender] = Role.X
 */
fun setRole(role: String) = assign(
    lhs = selfIndex(ROLE_MAPPING, msgSender),
    rhs = enumVal(ROLE_ENUM, role)
)

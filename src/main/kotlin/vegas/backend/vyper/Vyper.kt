package vegas.backend.vyper

// ========== Type System ==========

/**
 * SEMANTIC: Vyper type system has identical semantics to Solidity types.
 * Only syntactic differences in rendering (HashMap vs mapping, Bytes[N] vs bytes).
 */
sealed class VyType {
    // Primitive types
    object Int256 : VyType()
    object Uint256 : VyType()
    object Bool : VyType()
    object Address : VyType()
    object Bytes32 : VyType()
    data class DynBytes(val size: Int) : VyType()  // Vyper: Bytes[128]

    // Complex types
    data class HashMap(val keyType: VyType, val valueType: VyType) : VyType()
    data class EnumType(val name: String) : VyType()

    // Type name for rendering
    fun typeName(): String = when (this) {
        Int256 -> "int256"
        Uint256 -> "uint256"
        Bool -> "bool"
        Address -> "address"
        Bytes32 -> "bytes32"
        is DynBytes -> "Bytes[$size]"
        is HashMap -> "HashMap[${keyType.typeName()}, ${valueType.typeName()}]"
        is EnumType -> name
    }
}

// ========== Top Level Module ==========

/**
 * Complete Vyper module AST.
 * Vyper doesn't have contracts - everything is top-level declarations.
 */
data class VyperModule(
    val version: String = "0.4.0",
    val enums: List<EnumDecl>,
    val constants: List<ConstantDecl>,
    val storage: List<StorageDecl>,
    val constructor: Constructor,
    val functions: List<FunctionDecl>
)

// ========== Declarations ==========

data class EnumDecl(
    val name: String,
    val values: List<String>
)

data class ConstantDecl(
    val type: VyType,
    val name: String,
    val value: VyExpr
)

data class StorageDecl(
    val type: VyType,
    val name: String
    // No visibility in Vyper - all storage is private by default
)

data class Constructor(
    val body: List<Statement>
)

data class FunctionDecl(
    val name: String,
    val params: List<Param>,
    val decorators: List<Decorator>,  // @external, @payable, @view, @internal
    val body: List<Statement>
)

data class Param(
    val type: VyType,
    val name: String
)

// ========== Decorators ==========

sealed class Decorator {
    object External : Decorator()
    object Internal : Decorator()
    object Payable : Decorator()
    object View : Decorator()
    object Pure : Decorator()
}

// ========== Statements ==========

sealed class Statement {
    data class VarDecl(
        val type: VyType,
        val name: String,
        val init: VyExpr? = null
    ) : Statement()

    data class Assign(
        val lhs: VyExpr,
        val rhs: VyExpr
    ) : Statement()

    data class Assert(
        val condition: VyExpr,
        val message: String
    ) : Statement()

    data class If(
        val condition: VyExpr,
        val thenBranch: List<Statement>,
        val elseBranch: List<Statement> = emptyList()
    ) : Statement()

    data class Return(
        val value: VyExpr? = null
    ) : Statement()

    data class ExprStmt(
        val expr: VyExpr
    ) : Statement()

    object Pass : Statement()  // Vyper's no-op

    data class Raw(val code: String) : Statement()
}

// ========== Expressions ==========

/**
 * SEMANTIC: Expression semantics are identical to Solidity.
 * Only rendering differs (and/or/not vs &&/||/!, self. prefix).
 */
sealed class VyExpr {
    // Literals
    data class IntLit(val value: Int) : VyExpr()
    data class BoolLit(val value: Boolean) : VyExpr()
    data class StringLit(val value: String) : VyExpr()
    data class BytesLit(val value: String) : VyExpr()  // b"..."

    // Variables and access
    data class Var(val name: String) : VyExpr()
    data class SelfMember(val member: String) : VyExpr()  // self.x
    data class Member(val base: VyExpr, val member: String) : VyExpr()
    data class Index(val base: VyExpr, val index: VyExpr) : VyExpr()

    // Arithmetic (SEMANTIC: same as Solidity)
    data class Add(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Sub(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Mul(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Div(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Mod(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Neg(val operand: VyExpr) : VyExpr()

    // Comparison (SEMANTIC: same as Solidity)
    data class Eq(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Ne(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Lt(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Le(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Gt(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Ge(val left: VyExpr, val right: VyExpr) : VyExpr()

    // Boolean (SEMANTIC: same as Solidity)
    data class And(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Or(val left: VyExpr, val right: VyExpr) : VyExpr()
    data class Not(val operand: VyExpr) : VyExpr()

    // Ternary (Vyper uses if-else expressions, but rare)
    data class IfExpr(
        val condition: VyExpr,
        val ifTrue: VyExpr,
        val ifFalse: VyExpr
    ) : VyExpr()

    // Type operations
    data class Convert(val type: VyType, val operand: VyExpr) : VyExpr()  // convert(x, uint256)

    // Function calls
    data class Call(
        val function: String,
        val args: List<VyExpr>,
        val kwargs: Map<String, VyExpr> = emptyMap()  // For named arguments
    ) : VyExpr()

    // Built-ins (SEMANTIC: identical to Solidity)
    sealed class BuiltIn : VyExpr() {
        object MsgSender : BuiltIn()
        object MsgValue : BuiltIn()
        object BlockTimestamp : BuiltIn()
        object SelfAddress : BuiltIn()  // self (contract address)
        object Bytes32Zero : BuiltIn()
        object True : BuiltIn()
        object False : BuiltIn()
    }

    // Vyper-specific
    data class EnumValue(val enumType: String, val value: String) : VyExpr()

    data class AbiEncode(
        val args: List<VyExpr>,
        val outputType: VyType  // output_type parameter
    ) : VyExpr()

    data class Keccak256(val data: VyExpr) : VyExpr()

    data class RawCall(
        val target: VyExpr,
        val data: VyExpr,
        val value: VyExpr? = null,
        val maxOutsize: Int = 0,
        val gas: Int? = null  // Optional gas limit to prevent griefing attacks
    ) : VyExpr()
}

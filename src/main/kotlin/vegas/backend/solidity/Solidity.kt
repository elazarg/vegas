package vegas.backend.solidity

// ========== Type System ==========

sealed class SolType {
    // Primitive types
    object Int256 : SolType()
    object Uint256 : SolType()
    object Bool : SolType()
    object Address : SolType()
    object Bytes32 : SolType()
    object Bytes : SolType()  // Dynamic bytes array

    // Complex types
    data class Mapping(val keyType: SolType, val valueType: SolType) : SolType()
    data class EnumType(val name: String) : SolType()

    // Type name for rendering
    fun typeName(): String = when (this) {
        Int256 -> "int256"
        Uint256 -> "uint256"
        Bool -> "bool"
        Address -> "address"
        Bytes32 -> "bytes32"
        Bytes -> "bytes"
        is Mapping -> "mapping(${keyType.typeName()} => ${valueType.typeName()})"
        is EnumType -> name
    }
}

// ========== Top Level Contract ==========

/**
 * Complete Solidity contract AST.
 * Represents actual Solidity code structure.
 */
data class SolidityContract(
    val name: String,
    val constructor: Constructor,
    val enums: List<EnumDecl>,
    val storage: List<StorageDecl>,
    val modifiers: List<ModifierDecl>,
    val functions: List<FunctionDecl>,
    val events: List<EventDecl>,
    val fallback: FallbackDecl? = null
)

data class Constructor(
    val body: List<Statement>
)

// ========== Declarations ==========

data class EnumDecl(
    val name: String,
    val values: List<String>
)

data class StorageDecl(
    val type: SolType,
    val visibility: Visibility,
    val name: String,
    val constant: Boolean = false,
    val value: SolExpr? = null  // For constants
)

enum class Visibility { PUBLIC, PRIVATE, INTERNAL }

data class ModifierDecl(
    val name: String,
    val params: List<Param>,
    val body: List<Statement>
)

data class FunctionDecl(
    val name: String,
    val params: List<Param>,
    val visibility: Visibility,
    val stateMutability: StateMutability,
    val modifiers: List<ModifierCall>,
    val returns: List<Param> = emptyList(),
    val body: List<Statement>
)

data class Param(
    val type: SolType,
    val name: String
)

enum class StateMutability {
    PURE,      // Does not read or modify state
    VIEW,      // Reads but does not modify state
    PAYABLE,   // Can receive ether
    NONPAYABLE // Default: modifies state but cannot receive ether
}

data class ModifierCall(
    val name: String,
    val args: List<SolExpr> = emptyList()
)

data class EventDecl(
    val name: String,
    val params: List<Param> = emptyList()
)

data class FallbackDecl(
    val visibility: Visibility,
    val stateMutability: StateMutability,
    val body: List<Statement>
)

// ========== Statements ==========

sealed class Statement {
    /**
     * Local variable declaration with optional initialization.
     * Example: uint256 x = 10;
     */
    data class VarDecl(
        val type: SolType,
        val name: String,
        val init: SolExpr? = null
    ) : Statement()

    /**
     * Assignment statement.
     * LHS can be any lvalue (variable, mapping access, member access).
     * Example: x = 5; role[msg\.sender] = Role.Alice; balance = 100;
     */
    data class Assign(
        val lhs: SolExpr,
        val rhs: SolExpr
    ) : Statement()

    /**
     * Require statement with condition and error message.
     * Example: require(x > 0, "x must be positive");
     */
    data class Require(
        val condition: SolExpr,
        val message: String
    ) : Statement()

    /**
     * Revert statement.
     */
    data class Revert(
        val message: String
    ) : Statement()

    /**
     * Emit event.
     * Example: emit Transfer(from, to, amount);
     */
    data class Emit(
        val event: String,
        val args: List<SolExpr> = emptyList()
    ) : Statement()

    /**
     * If statement with optional else branch.
     */
    data class If(
        val condition: SolExpr,
        val thenBranch: List<Statement>,
        val elseBranch: List<Statement> = emptyList()
    ) : Statement()

    /**
     * Block of statements (for scoping).
     */
    data class Block(
        val statements: List<Statement>
    ) : Statement()

    /**
     * Return statement.
     */
    data class Return(
        val value: SolExpr? = null
    ) : Statement()

    /**
     * Expression statement (e.g., function call for side effects).
     */
    data class ExprStmt(
        val expr: SolExpr
    ) : Statement()

    /**
     * Raw Solidity code (escape hatch).
     * Use sparingly - prefer structured AST when possible.
     */
    data class Raw(val code: String) : Statement()
}

// ========== Expressions ==========

sealed class SolExpr {
    // ===== Literals =====

    data class IntLit(val value: Int) : SolExpr()
    data class BoolLit(val value: Boolean) : SolExpr()
    data class StringLit(val value: String) : SolExpr()
    data class AddressLit(val hex: String) : SolExpr()  // "0x..."

    // ===== Variables and Access =====

    /**
     * Simple variable reference.
     * Example: x, balance, myVar
     */
    data class Var(val name: String) : SolExpr()

    /**
     * Member access (dot notation).
     * Example: msg.sender, block.timestamp, myStruct.field
     */
    data class Member(val base: SolExpr, val member: String) : SolExpr()

    /**
     * Array/mapping index access.
     * Example: balances\[addr], array[i]
     */
    data class Index(val base: SolExpr, val index: SolExpr) : SolExpr()

    // ===== Arithmetic =====

    data class Add(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Sub(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Mul(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Div(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Mod(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Neg(val operand: SolExpr) : SolExpr()

    // ===== Comparison =====

    data class Eq(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Ne(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Lt(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Le(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Gt(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Ge(val left: SolExpr, val right: SolExpr) : SolExpr()

    // ===== Boolean Logic =====

    data class And(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Or(val left: SolExpr, val right: SolExpr) : SolExpr()
    data class Not(val operand: SolExpr) : SolExpr()

    // ===== Ternary =====

    data class Ternary(
        val condition: SolExpr,
        val ifTrue: SolExpr,
        val ifFalse: SolExpr
    ) : SolExpr()

    // ===== Type Operations =====

    /**
     * Type cast.
     * Example: uint256(x), address(addr)
     */
    data class Cast(val type: SolType, val operand: SolExpr) : SolExpr()

    // ===== Function Calls =====

    /**
     * Function call.
     * Example: keccak256(data), myFunc(x, y)
     */
    data class Call(
        val function: String,
        val args: List<SolExpr>
    ) : SolExpr()

    /**
     * Member function call.
     * Example: addr.call(data), token.transfer(to, amount)
     */
    data class MemberCall(
        val base: SolExpr,
        val function: String,
        val args: List<SolExpr>
    ) : SolExpr()

    /**
     * Function call with options (e.g., {value: amount, gas: limit}).
     * Example: addr.call{value: amount}(data)
     */
    data class CallWithOptions(
        val base: SolExpr,
        val function: String,
        val options: Map<String, SolExpr>,
        val args: List<SolExpr>
    ) : SolExpr()

    // ===== Solidity-Specific Built-ins =====

    /**
     * Built-in global variables and special values.
     */
    sealed class BuiltIn : SolExpr() {
        object MsgSender : BuiltIn()
        object MsgValue : BuiltIn()
        object BlockTimestamp : BuiltIn()
        object ThisAddress : BuiltIn()
        object Bytes32Zero : BuiltIn()
    }

    /**
     * Enum member access.
     * Example: Role.Alice, MyEnum.Value
     */
    data class EnumValue(val enumType: String, val value: String) : SolExpr()

    /**
     * ABI encoding - packed version.
     * Example: abi.encodePacked(x, y, z)
     */
    data class AbiEncodePacked(val args: List<SolExpr>) : SolExpr()

    /**
     * Keccak256 hash function.
     * Example: keccak256(data)
     */
    data class Keccak256(val data: SolExpr) : SolExpr()

    /**
     * Payable cast for addresses.
     * Example: payable(addr)
     */
    data class Payable(val address: SolExpr) : SolExpr()
}

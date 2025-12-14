package vegas.backend.solana

import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionId

// =========================================================================
// Types
// =========================================================================

sealed class SolanaType {
    object U8 : SolanaType()
    object U64 : SolanaType()
    object I64 : SolanaType()
    object Bool : SolanaType()
    object Pubkey : SolanaType()
    data class Array(val inner: SolanaType, val size: Int) : SolanaType()
    data class Vec(val inner: SolanaType) : SolanaType()
    object String : SolanaType()
    data class Custom(val name: String) : SolanaType()
}

// =========================================================================
// Program Structure
// =========================================================================

data class SolanaProgram(
    val name: String,
    val stateStruct: SolanaAccountStruct, // The main GameState PDA
    val errors: List<SolanaError>,
    val instructions: List<SolanaInstruction>,
    val additionalStructs: List<SolanaStruct> = emptyList(),
)

data class SolanaAccountStruct(
    val name: String,
    val fields: List<SolanaField>,
)

data class SolanaStruct(
    val name: String,
    val fields: List<SolanaField>,
)

data class SolanaField(
    val name: String,
    val type: SolanaType,
)

data class SolanaInstruction(
    val name: String,
    val accounts: List<SolanaAccountMeta>, // Accounts passed in Context
    val params: List<SolanaParam>,
    val body: List<SolanaStmt>,
)

data class SolanaParam(
    val name: String,
    val type: SolanaType,
)

data class SolanaAccountMeta(
    val name: String,
    val type: String, // e.g., "Account<'info, GameState>" or "Signer<'info>"
    val isMut: Boolean = false,
    val isSigner: Boolean = false, // Convenience to generate check if needed, mostly used for rendering
    val constraints: List<String> = emptyList(), // #[account(mut, has_one = ...)]
)

data class SolanaError(
    val name: String,
    val msg: String,
)

// =========================================================================
// Statements
// =========================================================================

sealed class SolanaStmt {
    data class Let(val name: String, val type: SolanaType?, val value: SolanaExpr) : SolanaStmt()
    data class Assign(val target: SolanaExpr, val value: SolanaExpr) : SolanaStmt()
    data class Require(val condition: SolanaExpr, val error: SolanaError) : SolanaStmt()
    data class If(val condition: SolanaExpr, val thenBranch: List<SolanaStmt>, val elseBranch: List<SolanaStmt> = emptyList()) : SolanaStmt()
    data class ExprStmt(val expr: SolanaExpr) : SolanaStmt()
    data class TransferSol(val from: String, val to: String, val amount: SolanaExpr) : SolanaStmt()
    data class Code(val text: String) : SolanaStmt()
    data class Comment(val text: String) : SolanaStmt()
}

// =========================================================================
// Expressions
// =========================================================================

sealed class SolanaExpr {
    // Literals
    data class IntLit(val v: Long) : SolanaExpr()
    data class BoolLit(val v: Boolean) : SolanaExpr()
    data class BytesLit(val bytes: List<Byte>) : SolanaExpr()
    data class StringLit(val v: String) : SolanaExpr()

    // References
    data class Var(val name: String) : SolanaExpr()
    data class FieldAccess(val target: SolanaExpr, val field: String) : SolanaExpr()
    data class Index(val target: SolanaExpr, val index: SolanaExpr) : SolanaExpr()

    // Operations
    data class Binary(val op: BinaryOp, val l: SolanaExpr, val r: SolanaExpr) : SolanaExpr()
    data class Unary(val op: UnaryOp, val expr: SolanaExpr) : SolanaExpr()

    // Built-ins
    object ClockTimestamp : SolanaExpr() // Clock::get()?.unix_timestamp
    data class PubkeyDefault(val pubkey: String = "default") : SolanaExpr() // Pubkey::default()

    // Calls
    data class Call(val func: String, val args: List<SolanaExpr>) : SolanaExpr()
    data class MethodCall(val target: SolanaExpr, val method: String, val args: List<SolanaExpr>) : SolanaExpr()

    data class If(val condition: SolanaExpr, val thenExpr: SolanaExpr, val elseExpr: SolanaExpr) : SolanaExpr()
    data class Raw(val text: String) : SolanaExpr()
}

enum class BinaryOp(val symbol: String) {
    ADD("+"), SUB("-"), MUL("*"), DIV("/"), MOD("%"),
    EQ("=="), NE("!="), LT("<"), LE("<="), GT(">"), GE(">="),
    AND("&&"), OR("||"), BIT_AND("&"), BIT_OR("|")
}

enum class UnaryOp(val symbol: String) {
    NOT("!"), NEG("-")
}

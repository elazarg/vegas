package vegas.backend.sui_move

/**
 * Sui Move Intermediate Representation.
 *
 * Represents the structure of a Sui Move Package.
 */

data class MovePackage(
    val name: String,
    val modules: List<MoveModule>
)

data class MoveModule(
    val name: String,
    val imports: Set<MoveImport>,
    val structs: List<MoveStruct>,
    val functions: List<MoveFunction>,
    val constants: List<MoveConst> = emptyList()
)

data class MoveImport(
    val address: String,
    val module: String,
    val alias: String? = null
)

data class MoveStruct(
    val name: String,
    val abilities: List<String>, // key, store, copy, drop
    val fields: List<MoveField>,
    val typeParams: List<String> = emptyList() // e.g. <phantom Asset>
)

data class MoveField(
    val name: String,
    val type: MoveType
)

data class MoveConst(
    val name: String,
    val type: MoveType,
    val value: MoveExpr
)

data class MoveFunction(
    val name: String,
    val visibility: MoveVisibility,
    val params: List<MoveParam>,
    val returnType: MoveType? = null,
    val body: List<MoveStmt>,
    val typeParams: List<String> = emptyList()
)

enum class MoveVisibility { PRIVATE, PUBLIC, PUBLIC_ENTRY, PUBLIC_FRIEND }

data class MoveParam(val name: String, val type: MoveType)

// ==========================================
// Statements
// ==========================================

sealed class MoveStmt {
    data class Let(val name: String, val type: MoveType? = null, val expr: MoveExpr) : MoveStmt()
    data class Assign(val lhs: MoveExpr, val rhs: MoveExpr) : MoveStmt() // *lhs = rhs or variable assignment if lhs is var
    data class Mutate(val lhs: MoveExpr, val rhs: MoveExpr) : MoveStmt() // *lhs = rhs
    data class Return(val expr: MoveExpr?) : MoveStmt()
    data class ExprStmt(val expr: MoveExpr) : MoveStmt()
    data class Assert(val cond: MoveExpr, val code: Long) : MoveStmt()
    data class If(val cond: MoveExpr, val thenBlock: List<MoveStmt>, val elseBlock: List<MoveStmt>? = null) : MoveStmt()
    data class Emit(val type: MoveType, val args: List<MoveFieldInit>) : MoveStmt()
    data class Comment(val text: String) : MoveStmt()
}

data class MoveFieldInit(val field: String, val value: MoveExpr)

// ==========================================
// Expressions
// ==========================================

sealed class MoveExpr {
    data class BoolLit(val value: Boolean) : MoveExpr()
    data class U64Lit(val value: Long) : MoveExpr()
    data class AddressLit(val value: String) : MoveExpr() // @0x...
    data class StringLit(val value: String) : MoveExpr() // b"..." for byte strings usually or string::utf8
    data class ByteStringLit(val value: String) : MoveExpr() // x"..."

    data class Var(val name: String) : MoveExpr()

    data class Call(val module: String?, val func: String, val typeArgs: List<MoveType> = emptyList(), val args: List<MoveExpr>) : MoveExpr()

    data class FieldAccess(val base: MoveExpr, val field: String) : MoveExpr()

    data class BinOp(val op: MoveBinOp, val lhs: MoveExpr, val rhs: MoveExpr) : MoveExpr()
    data class UnaryOp(val op: MoveUnaryOp, val arg: MoveExpr) : MoveExpr()

    data class StructInit(val type: MoveType, val fields: List<MoveFieldInit>) : MoveExpr()
    data class Vector(val items: List<MoveExpr>) : MoveExpr()

    data class Deref(val expr: MoveExpr) : MoveExpr() // *expr
    data class Borrow(val expr: MoveExpr, val mut: Boolean) : MoveExpr() // &expr or &mut expr

    // Explicit cast e.g. (x as u64)
    data class Cast(val expr: MoveExpr, val type: MoveType) : MoveExpr()

    data class IfElse(val cond: MoveExpr, val ifTrue: MoveExpr, val ifFalse: MoveExpr) : MoveExpr()
}

enum class MoveBinOp(val symbol: String) {
    ADD("+"), SUB("-"), MUL("*"), DIV("/"), MOD("%"),
    EQ("=="), NEQ("!="), LT("<"), LTE("<="), GT(">"), GTE(">="),
    AND("&&"), OR("||")
}

enum class MoveUnaryOp(val symbol: String) { NOT("!"), NEG("-") }

// ==========================================
// Types
// ==========================================

sealed class MoveType {
    object Bool : MoveType()
    object U8 : MoveType()
    object U64 : MoveType()
    object U128 : MoveType()
    object Address : MoveType()

    data class Struct(val module: String?, val name: String, val typeArgs: List<MoveType> = emptyList()) : MoveType()
    data class Vector(val param: MoveType) : MoveType()
    data class Ref(val param: MoveType, val mut: Boolean) : MoveType()
    data class TypeParam(val name: String) : MoveType()
}

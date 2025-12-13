package vegas.backend.evm

import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionId

/**
 * The "Game-Specific" EVM Intermediate Representation.
 *
 * This layer bridges the gap between abstract Game Theory (GameIR) and
 * concrete Blockchain Implementation (Solidity/Vyper).
 *
 * It reifies:
 * 1. The Storage Layout (Concrete slots vs abstract variables)
 * 2. The Execution Model (Imperative statements vs declarative rules)
 * 3. The Platform Context (Gas, Message Sender, Events)
 */

/**
 * Represents the complete implementation of a Vegas game on the EVM.
 *
 * Architecture:
 * - State: Concrete storage slots.
 * - Gameplay: A set of rigid, DAG-based Actions.
 * - Outcome: A terminal payoff calculation map.
 */
data class EvmContract(
    val name: String,
    val roles: List<RoleId>,

    // 1. THE STATE (Concrete Layout)
    val storage: List<EvmStorageSlot>,
    val enums: List<EvmEnum>,
    val events: List<EvmEvent>,

    // 2. THE GAMEPLAY (The DAG Implementation)
    // The explicit, rigid state machine nodes.
    val actions: List<EvmAction>,

    // Initialization logic (e.g. setting initial timestamps)
    val initialization: List<EvmStmt>,

    // Internal helpers (e.g. timeout checks)
    val helpers: List<EvmFunction> = emptyList(),

    // Global modifiers (e.g. depends, action)
    val modifiers: List<EvmModifier> = emptyList(),
)

/**
 * A rigid definition of a Game Move (Action).
 * This is the "Atomic Unit" of the state machine.
 *
 * It separates "Structural Constraints" (declarative) from
 * "Imperative Logic" (statements), allowing backends to render
 * them idiomatically (e.g. Modifiers vs. Asserts).
 */
data class EvmAction(
    val actionId: ActionId,
    val name: String,
    val invokedBy: RoleId,

    // The ABI Interface
    val inputs: List<EvmParam>,
    val payable: Boolean,              // True if this action accepts ETH (e.g. Join)

    // The State Machine Constraints (Declarative)
    val dependencies: List<ActionId>,  // List of ActionIDs that must be DONE
    val isTerminal: Boolean,           // If true, this action triggers the end-game check

    // The Imperative Logic
    // Contains ONLY the logic for this move (guards, storage updates, emits).
    // Generic logic (like checking 'actionDone' bitmaps) is implied by the
    // structural constraints above and injected by the renderer.

    // Declarative modifiers (Solidity)
    val modifiers: List<EvmExpr.Call> = emptyList(),
    // Equivalent inline checks (Vyper / generic)
    val checks: List<EvmStmt> = emptyList(),

    val guards: List<EvmExpr>,
    val body: List<EvmStmt>,

    // Post-action updates (Vyper / generic)
    val updates: List<EvmStmt> = emptyList()
)

/**
 * General purpose function (for helpers, internal logic).
 */
data class EvmFunction(
    val name: String,
    val inputs: List<EvmParam>,
    val visibility: String = "internal", // internal, private, public
    val mutability: String = "",         // view, pure
    val body: List<EvmStmt>
)

data class EvmModifier(
    val name: String,
    val params: List<EvmParam>,
    val body: List<EvmStmt>
)

// ==========================================
// Structural Definitions
// ==========================================

data class EvmStorageSlot(
    val name: String,
    val type: EvmType,
    val initialValue: EvmExpr? = null,
    val isImmutable: Boolean = false   // 'constant' in Sol / 'constant(...)' in Vyper
)

data class EvmEnum(
    val name: String,
    val values: List<String>
)

data class EvmEvent(
    val name: String,
    val params: List<EvmParam>
)

data class EvmParam(
    val name: VarId,
    val type: EvmType
)

// ==========================================
// Statements (Imperative Logic)
// ==========================================

sealed class EvmStmt {
    // Variable definition: `uint x = ...`
    data class VarDecl(val name: String, val type: EvmType, val init: EvmExpr? = null) : EvmStmt()

    // Assignment: `x = y` or `self.x = y`
    data class Assign(val lhs: EvmExpr, val rhs: EvmExpr) : EvmStmt()

    data class Return(val value: EvmExpr? = null) : EvmStmt()

    data class Emit(val eventName: String, val args: List<EvmExpr>) : EvmStmt()

    // Expressions as statements (e.g. void function calls)
    data class ExprStmt(val expr: EvmExpr) : EvmStmt()

    data class Require(val condition: EvmExpr, val message: String) : EvmStmt()

    // Hard stop
    data class Revert(val message: String) : EvmStmt()

    data class If(val condition: EvmExpr, val body: List<EvmStmt>, val elseBody: List<EvmStmt> = emptyList()) : EvmStmt()

    // Pass (No-op), useful for empty bodies in Vyper
    object Pass : EvmStmt()

    // Modifier placeholder '_;' (Solidity only)
    object Placeholder : EvmStmt()

    data class SendEth(val to: EvmExpr, val amount: EvmExpr) : EvmStmt()
}

// ==========================================
// Expressions (Value Logic)
// ==========================================

sealed class EvmExpr {
    // --- Literals ---
    data class IntLit(val value: Int) : EvmExpr()
    data class BoolLit(val value: Boolean) : EvmExpr()
    data class StringLit(val value: String) : EvmExpr()
    data class BytesLit(val value: String) : EvmExpr() // Hex string or raw bytes

    // --- Access ---
    data class Var(val name: VarId) : EvmExpr()
    data class Index(val base: EvmExpr, val index: EvmExpr) : EvmExpr()
    data class Member(val base: EvmExpr, val member: String) : EvmExpr()

    // --- Operations ---
    data class Unary(val op: UnaryOp, val arg: EvmExpr) : EvmExpr()
    data class Binary(val op: BinaryOp, val left: EvmExpr, val right: EvmExpr) : EvmExpr()
    data class Ternary(val cond: EvmExpr, val ifTrue: EvmExpr, val ifFalse: EvmExpr) : EvmExpr()

    // --- Calls ---
    data class Call(val func: String, val args: List<EvmExpr>) : EvmExpr()
    // For calling methods on objects (e.g. address.call(...))
    data class MemberCall(val base: EvmExpr, val func: String, val args: List<EvmExpr>) : EvmExpr()

    // --- Built-ins (Platform Intrinsics) ---
    sealed class BuiltIn : EvmExpr() {
        object MsgSender : BuiltIn()      // msg.sender
        object MsgValue : BuiltIn()       // msg.value
        object Timestamp : BuiltIn()      // block.timestamp
        object Self : BuiltIn()           // address(this) or self
    }

    // --- Special EVM Operations ---
    data class Keccak256(val data: EvmExpr) : EvmExpr()

    data class AbiEncode(
        val args: List<Var>,
        val isPacked: Boolean = false // packed for Sol, separate/raw for Vyper
    ) : EvmExpr()

    data class EnumValue(val enumName: String, val value: String) : EvmExpr()
}

enum class UnaryOp { NOT, NEG }

enum class BinaryOp {
    ADD, SUB, MUL, DIV, MOD,
    EQ, NE, LT, LE, GT, GE,
    AND, OR
}

// ==========================================
// Type System
// ==========================================

sealed class EvmType {
    object Int256 : EvmType()
    object Uint256 : EvmType() // Added Uint separate from Int
    object Bool : EvmType()
    object Address : EvmType()
    object Bytes32 : EvmType()

    // Abstracting Bytes vs Bytes[N]
    // Solidity: bytes (dynamic)
    // Vyper: Bytes[maxSize] (bounded)
    data class Bytes(val maxSize: Int = 1024) : EvmType()

    data class Mapping(val key: EvmType, val value: EvmType) : EvmType()
    data class EnumType(val name: String) : EvmType()

    // Helper for rendering to string in logs/debug
    fun typeName(): String = when(this) {
        Int256 -> "int256"
        Uint256 -> "uint256"
        Bool -> "bool"
        Address -> "address"
        Bytes32 -> "bytes32"
        is Bytes -> "bytes"
        is Mapping -> "mapping"
        is EnumType -> name
    }
}

package vegas.backend.evm

import vegas.RoleId
import vegas.VarId
import vegas.ir.NodeId

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
 * - Schedule: The event graph, with readiness-relative deadlines.
 * - Gameplay: One entry point per player-owned node.
 * - Outcome: One withdrawal per role.
 */
data class EvmContract(
    val name: String,
    val roles: List<RoleId>,

    // 1. THE STATE (Concrete Layout)
    val storage: List<EvmStorageSlot>,
    val enums: List<EvmEnum>,
    val events: List<EvmEvent>,

    // 2. THE SCHEDULE (when each node may happen, and what happens if it does not)
    val schedule: EvmSchedule,

    // 3. THE GAMEPLAY (player entry points, one per player-owned node)
    val actions: List<EvmAction>,

    // 4. THE OUTCOME
    val withdrawals: List<EvmWithdrawal>,

    // Initialization logic
    val initialization: List<EvmStmt>,

    // 5. TERMINAL AUDIT (null: plain settlement)
    val audit: EvmAudit? = null,
)

/**
 * Terminal-audit settlement.
 *
 * Every role posts [bonds] on top of its stake. Every move is bound to the
 * hash of the block in which its node became ready (`ctx`), so a signed move
 * proves it was created after that block. After play ends, anyone may submit
 * a transaction signed by a game account during [windowSeconds]; if it is not
 * a successfully executed call to this contract, the signer's bond is burned
 * (once). Settlement then returns unburned bonds with the payouts.
 */
data class EvmAudit(
    val bonds: Map<RoleId, Int>,
    val windowSeconds: Int,
)

/** Name of the readiness-context input of every audited move. */
val CONTEXT_PARAM = VarId("ctx")

/**
 * The event graph as the contract enforces it.
 *
 * Nodes are listed in a topological order and addressed by their position.
 * A node is *ready* once every predecessor is resolved; its readiness time
 * is the latest predecessor resolution (or deployment, for a source node).
 * It is *resolved* when it completes, or when it is resolved without a value:
 *  - its owner has already quit, at the later of readiness and the quit time;
 *  - its deadline `readiness + TIMEOUT` passed, at that deadline, which
 *    makes the owner quit (persistently, as in the analysis model);
 *  - the instance was aborted because a role never joined.
 * Only a ready node can expire, so a player is never blamed for a move it
 * could not yet make. Draw nodes never expire: they complete from the beacon.
 */
data class EvmSchedule(
    val nodes: List<EvmScheduleNode>,
    val draws: List<EvmDraw>,
) {
    init {
        nodes.forEachIndexed { i, n ->
            require(n.predecessors.all { it < i }) { "schedule is not topologically ordered at ${n.actionId}" }
        }
        require(nodes.size <= 256) { "schedule predecessor masks support at most 256 nodes" }
    }

    fun indexOf(id: NodeId): Int = nodes.indexOfFirst { it.actionId == id }.also {
        require(it >= 0) { "node $id is not scheduled" }
    }

    val usesBeacon: Boolean get() = draws.isNotEmpty()
}

enum class EvmNodeKind { JOIN, MOVE, DRAW }

data class EvmScheduleNode(
    val actionId: NodeId,
    val owner: RoleId,
    val predecessors: List<Int>,
    val kind: EvmNodeKind,
) {
    /** Predecessors as a bitmask over schedule positions. */
    val predecessorMask: java.math.BigInteger
        get() = predecessors.fold(java.math.BigInteger.ZERO) { m, j -> m.setBit(j) }
}

/**
 * The effect of a public draw: [body] stores the drawn value, reading the
 * beacon output as the local variable [BEACON_VALUE].
 */
data class EvmDraw(val node: Int, val body: List<EvmStmt>)

/** Name of the beacon output inside an [EvmDraw] body. */
val BEACON_VALUE = VarId("value")

/**
 * A role's withdrawal: [payout] once every node is resolved, or its own
 * deposit [refund] if the instance was aborted before play began.
 */
data class EvmWithdrawal(
    val role: RoleId,
    val name: String,
    val payout: EvmExpr,
    val refund: Int,
)

/**
 * A player entry point for one schedule node.
 * This is the "Atomic Unit" of the state machine.
 *
 * Structural constraints (turn, readiness, deadline) come from the node's
 * place in the [EvmSchedule] and are rendered by the backend; [guards] and
 * [body] hold only this move's own logic.
 */
data class EvmAction(
    val actionId: NodeId,
    val node: Int,
    val name: String,
    val invokedBy: RoleId,

    // The ABI Interface
    val inputs: List<EvmParam>,
    val payable: Boolean,              // True if this action accepts ETH (e.g. Join)
    val isJoin: Boolean,

    // The Imperative Logic
    val guards: List<EvmExpr>,
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

    // Pass (No-op), useful for empty bodies in Vyper
    object Pass : EvmStmt()

    data class SendEth(val to: EvmExpr, val amount: EvmExpr) : EvmStmt()

    /**
     * Verify a commitment-reveal: checks that
     *   _commitmentHash(role, msg.sender, abi.encode(payload...)) == commitment
     *
     * This binds commitments to role/actor/instance, preventing copy-commit attacks.
     * The actor is implicitly msg.sender - this is enforced by the type to prevent
     * accidentally passing the wrong actor.
     */
    data class CheckReveal(
        val commitment: EvmExpr,
        val role: RoleId,            // The role being revealed for
        val payload: List<EvmExpr>
    ) : EvmStmt()
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

    /**
     * abi.encode of arbitrary expressions (not just Vars). Used for
     * draw seed construction (beacon output, address(this), node index).
     * Distinct from [AbiEncode] which is wired to a specific commit-reveal
     * payload pattern.
     */
    data class AbiEncodeRaw(val args: List<EvmExpr>) : EvmExpr()

    /** Explicit conversion, e.g. of a literal to `int256`. */
    data class Cast(val type: EvmType, val arg: EvmExpr) : EvmExpr()

    data class EnumValue(val enumName: String, val value: String) : EvmExpr()
}

enum class UnaryOp { NOT, NEG }

enum class BinaryOp {
    ADD, SUB, MUL, DIV, MOD,
    EQ, NE, LT, LE, GT, GE,
    AND, OR
}

/**
 * Constants used across EVM backend code generation (Solidity, Vyper).
 */
object EvmConstants {
    /**
     * Default timeout in seconds (24 hours).
     */
    const val TIMEOUT_SECONDS = 86400

    /**
     * Default maximum size for bytes type.
     */
    const val DEFAULT_BYTES_SIZE = 1024
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
    data class Bytes(val maxSize: Int = EvmConstants.DEFAULT_BYTES_SIZE) : EvmType()

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

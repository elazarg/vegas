package vegas.backend.vyper

import vegas.RoleId
import vegas.VarId

/**
 * SEMANTIC: Naming scheme is identical to Solidity - these are semantic identifiers,
 * not syntactic ones. Only difference is rendering (self. prefix handled in ToText.kt).
 *
 * Centralized naming scheme for all Vyper identifiers.
 * Single source of truth for variable/function name generation.
 */

// ===== Storage Variables =====

fun storageParam(role: RoleId, param: VarId, hidden: Boolean): String {
    val prefix = if (hidden) "hidden_" else ""
    return "${role.name}_$prefix${param.name}"
}

fun doneFlag(role: RoleId, param: VarId, hidden: Boolean): String {
    return "done_${storageParam(role, param, hidden)}"
}

fun roleDone(role: RoleId): String {
    return "done_${role.name}"
}

fun roleAddr(role: RoleId): String = "address_${role.name}"

// ===== Functions =====

/**
 * Generate action function name (e.g., "move_Alice_0").
 * Used in DAG-based backend.
 */
fun actionFuncName(owner: RoleId, index: Int): String =
    "move_${owner.name}_$index"

/**
 * Generate action constant name (e.g., "ACTION_Alice_0").
 * Used in DAG-based backend.
 */
fun actionConstName(owner: RoleId, index: Int): String =
    "ACTION_${owner.name}_$index"

// ===== Parameters =====

fun inputParam(param: VarId, hidden: Boolean): String {
    val prefix = if (hidden) "hidden_" else ""
    return "_$prefix${param.name}"
}

// ===== Built-in Names =====

const val ROLE_ENUM = "Role"
const val ROLE_MAPPING = "role"
const val BALANCE_MAPPING = "balanceOf"
const val LAST_TS_VAR = "lastTs"

/**
 * SEMANTIC: Special "None" role represents unassigned addresses.
 */
val NO_ROLE = RoleId("None")

// ===== Configuration Constants =====

/**
 * Vyper version for generated contracts.
 */
const val VYPER_VERSION = "0.4.0"

/**
 * Gas limit for raw_call operations to prevent griefing attacks.
 * 100,000 gas is enough for simple transfers and some contract logic,
 * but not enough for complex reentrancy attacks.
 */
const val RAW_CALL_GAS_LIMIT = 100_000

/**
 * Maximum size for dynamic bytes in ABI encoding.
 * Used for commit-reveal scheme keccak256 inputs.
 */
const val ABI_ENCODE_BYTES_SIZE = 128

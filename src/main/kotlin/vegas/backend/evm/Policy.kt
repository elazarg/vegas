package vegas.backend.evm

import vegas.ir.QuitPolicy
import vegas.ir.ActionId
import vegas.RoleId

/**
 * A QuitPolicy that supports EVM code generation.
 *
 * Backends should cast the IR policy to this interface to access code generation methods.
 */
interface EvmQuitPolicy : QuitPolicy {
    /**
     * Additional storage required by the policy.
     */
    fun storage(): List<EvmStorageSlot>

    /**
     * Helper functions required by the policy.
     */
    fun helpers(): List<EvmFunction>

    /**
     * Returns modifier definitions for Solidity (e.g. 'depends', 'action').
     */
    fun solidityModifiersDefinition(): List<EvmModifier>

    /**
     * Generates the logic to run at the start of an action.
     * Used by backends that don't support modifiers (Vyper) or if modifiers are disabled.
     *
     * @param role The role performing the action.
     * @param actionId The action ID.
     * @param dependencies The list of actions this action depends on.
     * @return Statements to inject at the beginning of the action body.
     */
    fun preActionChecks(role: RoleId, actionId: ActionId, dependencies: List<ActionId>): List<EvmStmt>

    /**
     * Returns the modifier calls to apply to this action (Solidity).
     * e.g. `[Call("depends", ...), Call("action", ...)]`
     */
    fun actionModifiers(role: RoleId, actionId: ActionId, dependencies: List<ActionId>): List<EvmExpr.Call>

    /**
     * Generates the logic to run at the end of an action.
     * This typically includes:
     * - Marking the action as done
     * - Updating timestamps
     *
     * @param role The role performing the action.
     * @param actionId The action ID.
     * @return Statements to inject at the end of the action body.
     */
    fun postActionLogic(role: RoleId, actionId: ActionId): List<EvmStmt>
}

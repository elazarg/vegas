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
     * Generates the logic to run at the start of an action.
     * This typically includes:
     * - Verifying the invoker (msg.sender)
     * - Checking if the action is already done
     * - Checking dependencies (Policy specific)
     * - Checking for timeouts/bailouts (Policy specific)
     *
     * @param role The role performing the action.
     * @param actionId The action ID.
     * @param dependencies The list of actions this action depends on.
     * @return Statements to inject at the beginning of the action body.
     */
    fun preActionLogic(role: RoleId, actionId: ActionId, dependencies: List<ActionId>): List<EvmStmt>

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

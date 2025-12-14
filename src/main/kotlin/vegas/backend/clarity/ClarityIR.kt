package vegas.backend.clarity

import vegas.RoleId
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.Type

/**
 * Clean IR for Clarity backend.
 * Represents the game as a set of Actions (dependencies) + Timeout Rules.
 */
internal data class ClarityGame(
    val name: String,
    val roles: List<RoleId>,
    val pot: Long,
    val actions: List<ClarityAction>,
    val timeoutRules: List<TimeoutRule>,
    val terminalFrontiers: List<Set<ActionId>>,
    val payoffs: Map<RoleId, Expr>
)

internal data class ClarityAction(
    val id: ActionId,
    val owner: RoleId,
    val prereqs: Set<ActionId>,
    val params: List<ClarityParam>,
    // If commit: we store the hash.
    // If reveal: we verify hash and store value.
    // If public: we store value.
    val type: ActionType,
    val writes: List<ClarityStateVar>,
    val guard: Expr?
)

internal sealed class ActionType {
    object Commit : ActionType()
    data class Reveal(val commitVar: String) : ActionType() // References the variable holding the commit
    object Public : ActionType()
}

internal data class ClarityParam(
    val name: String,
    val type: Type,
    val isSalt: Boolean = false // If true, this is the salt for a reveal
)

internal data class ClarityStateVar(
    val name: String,
    val type: Type, // If Commit, this is Buff 32 (implicit)
    val isCommit: Boolean
)

internal data class TimeoutRule(
    val required: Set<ActionId>, // Actions that MUST be done
    val forbidden: Set<ActionId>, // Actions that MUST NOT be done (to distinguish from next frontier)
    val payoff: Map<RoleId, Long>
)

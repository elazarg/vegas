package vegas.backend.gambit

import vegas.Rational
import vegas.RoleId
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.ActionId
import vegas.ir.GameIR

/**
 * Converts LTS semantics into a GameTree by unrolling configurations.
 *
 * This is the bridge between the semantic model (Configuration + Labels)
 * and the EFG tree representation. Uses [ExpansionPolicy] to control
 * which branches to expand immediately vs defer as [GameTree.Continuation].
 *
 * TreeUnroller interprets move labels from [GameSemantics] and builds tree structure.
 * It handles tree-specific concerns like quit-only decision nodes for roles with
 * no parameters or roles that have already quit (abandonment persistence).
 */
internal class TreeUnroller(
    private val semantics: GameSemantics,
    private val ir: GameIR
) {
    private val infosetManager = UnrollerInfosetManager(ir.roles)

    /**
     * Unroll the LTS from a configuration into a GameTree.
     *
     * Uses canonical role ordering (alphabetical by name) to ensure
     * deterministic tree structure.
     *
     * @param config Starting configuration
     * @param policy Expansion policy for strategic choices
     * @return Game subtree rooted at this configuration
     */
    fun unroll(config: Configuration, policy: ExpansionPolicy): GameTree {
        // Terminal check
        if (config.isTerminal()) {
            return GameTree.Terminal(computePayoffs(config))
        }

        // Get all moves via semantic layer
        val moves = semantics.enabledMoves(config)

        // Group by role in canonical order and build tree
        return buildTreeFromMoves(config, moves, policy)
    }

    private fun buildTreeFromMoves(
        config: Configuration,
        moves: List<Label>,
        policy: ExpansionPolicy
    ): GameTree {
        // Filter out FinalizeFrontier - it's implicit in tree structure
        val playMoves = moves.filterIsInstance<Label.Play>()

        // Group by role, maintaining canonical order
        val movesByRole = playMoves.groupBy({ it.role }, { it })
        val rolesInOrder = movesByRole.keys.sortedBy { it.name }

        // Build tree by iterating through roles, creating decision nodes
        return buildRoleDecisions(
            config = config,
            roles = rolesInOrder,
            movesByRole = movesByRole,
            roleIndex = 0,
            policy = policy
        )
    }

    private fun buildRoleDecisions(
        config: Configuration,
        roles: List<RoleId>,
        movesByRole: Map<RoleId, List<Label.Play>>,
        roleIndex: Int,
        policy: ExpansionPolicy
    ): GameTree {
        // All roles done: apply FinalizeFrontier if enabled
        if (roleIndex == roles.size) {
            return if (semantics.canFinalizeFrontier(config)) {
                val nextConfig = semantics.applyMove(config, Label.FinalizeFrontier)
                unroll(nextConfig, policy)
            } else {
                error("Reached end of role loop but FinalizeFrontier not enabled")
            }
        }

        val role = roles[roleIndex]
        var roleMoves = movesByRole[role]
        val isChance = role in ir.chanceRoles

        // Handle roles that need quit-only decision nodes when policy allows abandonment
        // This happens in two cases:
        // 1. Role has actions but no parameters (e.g., reveal with pre-assigned value)
        // 2. Role has already quit in history (but has actions in current frontier)
        if ((roleMoves == null || roleMoves.isEmpty()) && !isChance) {
            val actionsForRole = config.actionsByRole(ir.dag)[role]
            if (actionsForRole != null && actionsForRole.isNotEmpty()) {
                val allParams = actionsForRole.flatMap { ir.dag.params(it) }
                val hasQuit = config.history.quit(role)

                // Create quit-only node if:
                // - Role has no parameters (empty params), OR
                // - Role has already quit (persistence of abandonment)
                if ((allParams.isEmpty() || hasQuit) && policy.shouldExpand(role, null)) {
                    // Synthesize a quit move with empty delta
                    val quitMove = Label.Play(role, emptyMap(), PlayTag.Quit)
                    roleMoves = listOf(quitMove)
                }
            }
        }

        // If still no moves, skip to next role
        if (roleMoves == null || roleMoves.isEmpty()) {
            return buildRoleDecisions(config, roles, movesByRole, roleIndex + 1, policy)
        }

        // Compute infoset ID
        val views = config.views(ir.roles + ir.chanceRoles)
        val infoset = views.getValue(role)
        val infosetId = infosetManager.getHistoryNumber(role, infoset, isChance)

        // Build choices for this role
        val choices = roleMoves.map { playMove ->
            val shouldExpand = when (playMove.tag) {
                is PlayTag.Action -> {
                    // Chance always expands, strategic consults policy
                    isChance || policy.shouldExpand(role, playMove.tag.actionId)
                }
                is PlayTag.Quit -> {
                    policy.shouldExpand(role, null)
                }
            }

            val subtree = if (shouldExpand) {
                // Expand: apply move and recurse to next role
                val nextConfig = semantics.applyMove(config, playMove)
                buildRoleDecisions(nextConfig, roles, movesByRole, roleIndex + 1, policy)
            } else {
                // Defer: create Continuation
                val nextConfig = semantics.applyMove(config, playMove)
                GameTree.Continuation(
                    GeneratorContext(
                        frontier = nextConfig.frontier,
                        history = nextConfig.history,
                        partialFrontierAssignment = nextConfig.partial,
                        actionId = (playMove.tag as? PlayTag.Action)?.actionId
                    )
                )
            }

            GameTree.Choice(
                action = extractActionLabel(playMove.delta, role),
                subtree = subtree,
                probability = if (isChance) Rational(1, roleMoves.size) else null
            )
        }

        return GameTree.Decision(
            owner = role,
            infosetId = infosetId,
            choices = choices,
            isChance = isChance
        )
    }

    private fun computePayoffs(config: Configuration): Map<RoleId, IrVal> {
        return ir.payoffs.mapValues { (_, expr) ->
            eval({ config.history.get(it) }, expr).toOutcome()
        }
    }
}

/**
 * Manages information set identification and numbering during tree unrolling.
 *
 * Each strategic role gets a separate numbering space based on its information
 * (player view/history). Chance nodes get unique sequential numbers.
 */
private class UnrollerInfosetManager(roles: Set<RoleId>) {
    private val perRole: Map<RoleId, MutableMap<History, Int>> = roles.associateWith { mutableMapOf() }
    private var chanceCounter: Int = 0

    fun getHistoryNumber(role: RoleId, key: History, isChance: Boolean): Int {
        if (isChance) {
            chanceCounter += 1
            return chanceCounter
        }
        val table = perRole.getValue(role)
        return table.getOrPut(key) { table.size }
    }
}

/**
 * Extract action label for this role from frontier delta.
 *
 * Filters to only this role's non-Quit fields and unwraps to VarId -> IrVal.
 */
private fun extractActionLabel(frontierDelta: FrontierAssignmentSlice, role: RoleId): Map<VarId, IrVal> =
    frontierDelta
        .filterKeys { fr -> fr.owner == role }
        .filterValues { v -> v != IrVal.Quit }
        .mapKeys { (fr, _) -> fr.param }

/**
 * # Gambit EFG Backend
 *
 * This package converts Vegas ActionDag IR into Gambit's Extensive Form Game (EFG) format.
 *
 * ## Architecture
 *
 * **Pipeline**: `GameIR -> GameTree -> EFG String`
 *
 * 3. **FromIR.kt** - Main algorithm: IR -> GameTree conversion via frontier exploration
 * 4. **Gambit.kt** - Game tree data structure (Decision/Terminal nodes)
 * 5. **ToText.kt** - EFG text format serialization
 *
 * ## Key Concepts
 *
 * - **Frontier-based exploration**: Each frontier becomes a simultaneous-move round
 * - **Perfect recall**: Information sets keyed by complete redacted history (History stack)
 * - **Commit/Reveal**: Information hiding via Hidden -> Opaque transformation
 * - **Epistemic layering**: Each frontier slice represents one layer of observations
 *
 * ## Entry Point
 *
 * ```kotlin
 * generateExtensiveFormGame(ir: GameIR, happyOnly: Boolean = false): String
 * ```
 */
package vegas.backend.gambit

import vegas.Rational
import vegas.RoleId
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.toOutcome
import vegas.semantics.Configuration
import vegas.semantics.FrontierAssignmentSlice
import vegas.semantics.GameSemantics
import vegas.semantics.History
import vegas.semantics.Label
import vegas.semantics.PlayTag
import vegas.semantics.applyMove
import vegas.semantics.eval
import vegas.semantics.quit
import vegas.semantics.reconstructViews

/**
 * Functional interface determining which actions to expand during generation.
 *
 * The policy is checked for each (role, action) combination:
 * - true: Generate subtree recursively (immediate expansion)
 * - false: Create Continuation node (deferred expansion)
 *
 * Chance nodes ALWAYS expand regardless of policy.
 */
fun interface ExpansionPolicy {
    /**
     * Determines whether to expand a specific action.
     *
     * @param owner The role making the decision
     * @param action The action being considered (null = quit)
     * @return true to expand immediately, false to create Continuation
     */
    fun shouldExpand(owner: RoleId, action: ActionId?): Boolean


    companion object {
        /**
         * FAIR_PLAY: Expand all explicit moves, defer abandonment branches.
         *
         * This is the default policy and produces the "spine" tree:
         * - Focuses on strategic play where players actively participate
         * - Abandonment branches can be added later via expand()
         * - Equivalent to old SPINE_ONLY mode
         */
        val FAIR_PLAY: ExpansionPolicy = ExpansionPolicy { _, action -> action != null }

        /**
         * FULL_EXPANSION: Expand everything including abandonment branches.
         *
         * Produces the complete game tree with all possible paths:
         * - Used for game-theoretic verification
         * - Includes all abandonment/griefing scenarios
         * - Equivalent to old FULL_EXPANSION mode
         * - WARNING: Exponentially larger trees
         */
        val FULL_EXPANSION: ExpansionPolicy = ExpansionPolicy { _, _ -> true }

        /**
         * SKELETON: Defer everything, create minimal tree structure.
         *
         * Produces a tree with all branches suspended:
         * - Useful for analyzing game structure without generating full tree
         * - Can selectively expand interesting branches
         */
        val SKELETON: ExpansionPolicy = ExpansionPolicy { _, _ -> false }
    }
}

/**
 * Build a Gambit EFG string from the ActionDag-based IR.
 *
 * Uses policy-driven generation with optional abandonment branch inclusion.
 *
 * Semantics (informally):
 *
 *  - The ActionDag is a partial order of actions. At runtime, we explore it by
 *    repeatedly taking a *frontier* of currently enabled actions. Each resolved
 *    frontier contributes one "epistemic layer" of writes along a history.
 *
 *  - Global history is represented as a stack of frontier slices:
 *      each slice is a map from (role, variable) to the Expr.Const written by some
 *      action in that frontier.  The stack order is the order in which frontiers
 *      are resolved along that history.
 *
 *  - Each player maintains a parallel stack of *redacted* slices (a HistoryViews):
 *      * their own fields are seen with their actual values;
 *      * other players' committed (hidden) values appear as Quit;
 *      * Quit is used for abandonment ("quit") and is never hidden.
 *
 *  - An information set for a role is keyed purely by that role's redacted stack.
 *    This yields perfect recall in the usual extensive-form sense: the role can
 *    always recover what it has previously done and observed.
 *
 *  - Each resolved frontier is treated as a simultaneous-move round:
 *      * all actions enabled in that frontier execute exactly once per history;
 *      * for each role we enumerate joint assignments for all of its actions in that
 *        frontier (subject to guards);
 *      * after all roles choose, the resulting frontier slice is pushed onto the
 *        global history and all players' knowledge stacks.
 *
 * This layering is epistemic, not part of the IR itself: it is induced by the
 * frontier exploration of the ActionDag and respects its causal partial order.
 */
fun generateExtensiveFormGame(ir: GameIR, includeAbandonment: Boolean = true): String {
    // Use new semantic + unroller API (semantic refactoring complete)
    val semantics = GameSemantics(ir)
    val unroller = TreeUnroller(semantics, ir)

    val policy = if (includeAbandonment) {
        ExpansionPolicy.FULL_EXPANSION
    } else {
        ExpansionPolicy .FAIR_PLAY
    }

    val initialConfig = Configuration(
        frontier = FrontierMachine.from(ir.dag),
        history = History()
    )

    var tree = unroller.unroll(initialConfig, policy)
    tree = pruneContinuations(tree)

    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from ActionDag",
        strategicPlayers = ir.roles,
        tree = tree
    ).toEfg()
}


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
    private val infosetManager = InfosetManager(ir.roles)

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
                val nextConfig = applyMove(config, Label.FinalizeFrontier)
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
        val views = reconstructViews(config.history, ir.roles + ir.chanceRoles)
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
                val nextConfig = applyMove(config, playMove)
                buildRoleDecisions(nextConfig, roles, movesByRole, roleIndex + 1, policy)
            } else {
                // Defer: create Continuation
                val nextConfig = applyMove(config, playMove)
                GameTree.Continuation(
                    GeneratorContext(
                        configuration = nextConfig,
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

    private fun computePayoffs(config: Configuration): Map<RoleId, Expr.Const> {
        fun computeUtility(role: RoleId, expr: Expr): Expr.Const.IntVal {
            val deposit: Expr.Const.IntVal = ir.dag.deposit(role)
            val outcome: Expr.Const.IntVal = eval({ config.history.get(it) }, expr).toOutcome()
            return Expr.Const.IntVal(outcome.v - deposit.v)
        }
        return ir.payoffs.mapValues { (role, expr) -> computeUtility(role, expr) }
    }
}


/**
 * Remove all Continuation nodes from the tree by mutating Choice.subtree fields.
 *
 * Instead of removing choices, we leverage that Choice.subtree is mutable (var).
 * We filter out choices that lead to Continuations and reconstruct Decision nodes.
 */
internal fun pruneContinuations(node: GameTree): GameTree {
    return when (node) {
        is GameTree.Terminal -> node
        is GameTree.Continuation -> node // Should not happen at top level
        is GameTree.Decision -> {
            // Filter out choices leading to Continuation nodes
            val prunedChoices = node.choices
                .filter { it.subtree !is GameTree.Continuation }
                .map { choice ->
                    // Recursively prune subtrees
                    choice.copy(subtree = pruneContinuations(choice.subtree))
                }

            // If no choices remain after pruning, this is an error
            // (should not happen in well-formed trees)
            if (prunedChoices.isEmpty()) {
                error("Decision node has no choices after pruning Continuations")
            }

            // Create new Decision node with pruned choices
            node.copy(choices = prunedChoices)
        }
    }
}

/**
 * Manages information set identification and numbering during game tree construction.
 *
 * **Strategic players**: Information sets are identified by the player's complete redacted
 * knowledge history (stack of frontier slices they observed). The first time a particular
 * history is seen, it's assigned a new infoset number. Perfect recall is maintained because
 * the history captures everything the player has observed.
 *
 * **Chance nodes**: Each chance decision receives a unique sequential number, as chance
 * nodes don't have information sets in the game-theoretic sense.
 *
 * This is mutable history intended to be scoped to a single game tree build.
 *
 * @param roles Set of strategic player role IDs (chance roles excluded)
 */
private class InfosetManager(roles: Set<RoleId>) {
    private val perRole: Map<RoleId, MutableMap<History, Int>> = roles.associateWith { mutableMapOf() }
    private var chanceCounter: Int = 0

    fun getHistoryNumber(role: RoleId, key: History, isChance: Boolean): Int {
        if (isChance) {
            chanceCounter += 1
            return chanceCounter
        }
        val table = perRole.getValue(role)
        return table.getOrPut(key) { table.size } // 0-based is fine; writer will shift if needed
    }
}

/**
 * Minimal context required to resume generation at a decision point.
 */
internal data class GeneratorContext(
    val configuration: Configuration,
    // The "Edge Identity" (For Policy / Resume)
    val actionId: ActionId?
)


/**
 * Extract action label for this role from frontier delta.
 *
 * Filters to only this role's non-Quit fields and unwraps to VarId -> Expr.Const.
 */
private fun extractActionLabel(frontierDelta: FrontierAssignmentSlice, role: RoleId): Map<VarId, Expr.Const> =
    frontierDelta
        .filterKeys { fr -> fr.owner == role }
        .filterValues { v -> v != Expr.Const.Quit }
        .mapKeys { (fr, _) -> fr.param }

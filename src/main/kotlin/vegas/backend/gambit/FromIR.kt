/**
 * # Gambit EFG Backend
 *
 * This package converts Vegas EventGraph IR into Gambit's Extensive Form Game (EFG) format.
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
import vegas.StaticError
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.NodeId
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.SampleSpec
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
    fun shouldExpand(owner: RoleId, action: NodeId?): Boolean


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
 * Build a Gambit EFG string from the EventGraph-based IR.
 *
 * Uses policy-driven generation with optional abandonment branch inclusion.
 *
 * Semantics (informally):
 *
 *  - The EventGraph is a partial order of actions. At runtime, we explore it by
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
 * frontier exploration of the EventGraph and respects its causal partial order.
 */
/**
 * Distinct from generic [StaticError] so the conservation pass can
 * distinguish "the program violates conservation" from "the strategic
 * tree could not be enumerated" (unbounded int types, pruning artifacts,
 * etc.). Only [ConservationViolation] propagates from [verifyConservation];
 * enumeration failures are swallowed and the program is accepted on a
 * best-effort basis. A future symbolic SMT-based check would close this
 * gap (see FUTURE.md).
 */
internal class ConservationViolation(message: String) : StaticError(message)

/**
 * Verify pot conservation at every reachable terminal of the strategic
 * game tree (no abandonment branches; quit moves don't model what we
 * mean by "the game completed"). At each terminal, the equation
 * `sum(payoffs) + burn == 0` must hold, since payoffs are computed
 * net of deposits and the strategic pot equals the deposits. Throws
 * [ConservationViolation] with the failing terminal's history on the
 * first violation; iterates left-to-right deterministically.
 *
 * The check piggybacks on the existing Gambit tree unroller (so
 * sample/chance branches are enumerated correctly, with the same
 * conditioning semantics that EFG output uses). It runs the
 * FAIR_PLAY policy and prunes continuations.
 *
 * Games whose tree Gambit cannot fully enumerate (unbounded int types,
 * unsupported patterns) are skipped silently; only programs that Gambit
 * can analyze AND that violate conservation are rejected.
 */
fun verifyConservation(ir: GameIR) {
    val tree = try {
        val semantics = GameSemantics(ir)
        val unroller = TreeUnroller(semantics, ir, failOnDeadChoices = true)
        val initial = Configuration(
            frontier = FrontierMachine.from(ir.dag),
            history = History(),
        )
        pruneContinuations(unroller.unroll(initial, ExpansionPolicy.FAIR_PLAY))
    } catch (e: StaticError) {
        if (e is ConservationViolation) throw e
        return // enumeration failure: accept best-effort
    } catch (_: IllegalStateException) {
        return // pruning artifact: accept best-effort
    }
    walkAndCheck(tree, history = emptyList())
}

private fun walkAndCheck(node: GameTree, history: List<String>) {
    when (node) {
        is GameTree.Terminal -> {
            val sumPayoffs = node.payoffs.values.sumOf { (it as Expr.Const.IntVal).v }
            val burn = node.burn.v
            val total = sumPayoffs + burn
            if (total != 0) {
                val payoffLines = node.payoffs.entries.joinToString("; ") { (r, v) ->
                    "${r.name} -> ${(v as Expr.Const.IntVal).v} (utility, net of deposit)"
                }
                val pathText = if (history.isEmpty()) "<root>" else history.joinToString(" -> ")
                throw ConservationViolation(
                    "Pot conservation violation at terminal [$pathText]:\n" +
                        "  $payoffLines\n" +
                        "  burn = $burn\n" +
                        "  sum(utility) + burn = $total (expected 0; equivalently sum(gross payouts) + burn == sum(deposits))",
                )
            }
        }
        is GameTree.Decision -> {
            for (choice in node.choices) {
                val actionStr = choice.action.entries.joinToString(",") { (k, v) -> "${k.name}=$v" }
                val step = "${node.owner.name}{$actionStr}"
                walkAndCheck(choice.subtree, history + step)
            }
        }
        is GameTree.Continuation -> { /* pruned before walk; no-op */ }
    }
}

fun generateExtensiveFormGame(
    ir: GameIR,
    includeAbandonment: Boolean = true,
    failOnDeadChoices: Boolean = true,
): String {
    val semantics = GameSemantics(ir)
    val unroller = TreeUnroller(semantics, ir, failOnDeadChoices)

    val policy = if (includeAbandonment) {
        ExpansionPolicy.FULL_EXPANSION
    } else {
        ExpansionPolicy.FAIR_PLAY
    }

    val initialConfig = Configuration(
        frontier = FrontierMachine.from(ir.dag),
        history = History()
    )

    var tree = unroller.unroll(initialConfig, policy)
    tree = pruneContinuations(tree)

    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from EventGraph",
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
    private val ir: GameIR,
    private val failOnDeadChoices: Boolean = true
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
        if (config.isTerminal()) {
            return GameTree.Terminal(computePayoffs(config), computeBurn(config))
        }
        val moves = semantics.enabledMoves(config)
        return buildTreeFromMoves(config, moves, policy)
    }

    private fun computeBurn(config: Configuration): Expr.Const.IntVal =
        eval({ config.history.get(it) }, ir.burn).toOutcome()

    private fun buildTreeFromMoves(
        config: Configuration,
        moves: List<Label>,
        policy: ExpansionPolicy
    ): GameTree {
        // Filter out FinalizeFrontier - it's implicit in tree structure
        val playMoves = moves.filterIsInstance<Label.Play>()

        // Group by role, maintaining canonical order
        val movesByRole = playMoves.groupBy({ it.role }, { it })

        // Chance roles with actions but no surviving moves never appear in
        // movesByRole because enabledMoves does not synthesize a quit move
        // for them. Without visiting them, the dead-choice check cannot
        // fire and an unsatisfiable sample guard falls through to the
        // internal FinalizeFrontier error.
        val actionsByRole = config.actionsByRole(ir.dag)
        val deadChanceRoles = actionsByRole.keys.filter { role ->
            role !in movesByRole &&
                actionsByRole.getValue(role).any { ir.dag.isSampleNode(it) && ir.dag.params(it).isNotEmpty() }
        }
        val rolesInOrder = (movesByRole.keys + deadChanceRoles).sortedBy { it.name }

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

        val actionsForRole = config.actionsByRole(ir.dag)[role].orEmpty()
        // A role's decision at this frontier is a chance node iff every
        // action it owns here is a sample node. Mixing is currently
        // unrepresentable in the surface language and is asserted away.
        val sampleFlags = actionsForRole.map { ir.dag.isSampleNode(it) }
        val isChance: Boolean = when {
            sampleFlags.isEmpty() -> false
            sampleFlags.all { it } -> true
            sampleFlags.none { it } -> false
            else -> error("Mixed sample/strategic actions for role ${role.name} at the current frontier")
        }
        val allParams = actionsForRole.flatMap { ir.dag.params(it) }
        val hasQuit = config.history.quit(role)

        // If the role has parameterized actions "in scope" but no enabled moves,
        // we treat it as a static error (unsatisfiable where/guards), unless role
        // already quit. This applies to chance roles too: a Sample whose guard
        // kills every value in its dist support is malformed, not a fallback.
        if (
            failOnDeadChoices &&
            !hasQuit &&
            actionsForRole.isNotEmpty() &&
            allParams.isNotEmpty() &&
            (roleMoves.isNullOrEmpty())
        ) {
            val actionIds = actionsForRole.joinToString(", ")
            val paramIds = allParams.joinToString(", ")
            throw StaticError(
                buildString {
                    appendLine("Dead choice set detected for role=${role.name}.")
                    appendLine("Frontier has actions for this role, but enabledMoves produced no legal plays.")
                    appendLine("This usually means a `where`/guard is unsatisfiable in some reachable state.")
                    appendLine("Actions: $actionIds")
                    appendLine("Params:  $paramIds")
                    appendLine("History: ${config.history}")
                    appendLine("Hint: add an explicit null/else branch or widen the domain/guards.")
                }
            )
        }

        // Existing quit-only synthesis (now uses precomputed values)
        if (roleMoves.isNullOrEmpty() && !isChance) {
            if (actionsForRole.isNotEmpty()) {
                // allParams, hasQuit already computed above

                if ((allParams.isEmpty() || hasQuit) && policy.shouldExpand(role, null)) {
                    val quitMove = Label.Play(role, emptyMap(), PlayTag.Quit)
                    roleMoves = listOf(quitMove)
                }
            }
        }

        if (roleMoves.isNullOrEmpty()) {
            return buildRoleDecisions(config, roles, movesByRole, roleIndex + 1, policy)
        }

        // Compute infoset ID
        val views = reconstructViews(config.history, ir.roles + ir.chanceRoles)
        val infoset = views.getValue(role)
        val infosetId = infosetManager.getHistoryNumber(role, infoset, isChance)

        // Per-move chance probabilities, renormalized over the guard-surviving
        // support so they sum to 1 across this node's children.
        val chanceProbs: Map<Label.Play, Rational> =
            if (isChance) computeChanceProbabilities(roleMoves) else emptyMap()

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
                probability = if (isChance) chanceProbs.getValue(playMove) else null
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

    /**
     * Per-move chance probabilities at a single chance decision, renormalized
     * over the guard-surviving moves so they sum to 1.
     *
     * If every Action move's Sample node carries an explicit Dist, each
     * move's probability is `dist.weight(value) / sum(weights)`. If any
     * move lacks an explicit Dist (multi-parameter chance node, unbounded
     * domain), we fall back to uniform over surviving moves, which is the
     * same answer the explicit path gives when the underlying dist is uniform.
     */
    private fun computeChanceProbabilities(
        roleMoves: List<Label.Play>,
    ): Map<Label.Play, Rational> {
        if (roleMoves.isEmpty()) return emptyMap()

        val priors: List<Rational?> = roleMoves.map { move -> priorWeight(move) }
        val allDeclared = priors.all { it != null }

        if (!allDeclared) {
            val uniform = Rational(1, roleMoves.size)
            return roleMoves.associateWith { uniform }
        }

        val total = priors.filterNotNull().reduce { a, b -> a + b }
        if (total == Rational(0)) {
            val uniform = Rational(1, roleMoves.size)
            return roleMoves.associateWith { uniform }
        }
        return roleMoves.zip(priors).associate { (move, w) ->
            move to (w!! / total)
        }
    }

    /**
     * Prior weight of a single chance move under its Sample node's declared
     * distribution, or null if no explicit distribution applies.
     */
    private fun priorWeight(move: Label.Play): Rational? {
        val actionId = (move.tag as? PlayTag.Action)?.actionId ?: return null
        val spec: SampleSpec = ir.dag.sampleSpec(actionId) ?: return null
        val dist = spec.dist ?: return null
        // Single-parameter sample only: the move's delta has one entry whose
        // value is the sampled Const. Multi-parameter samples are rejected
        // upstream (Dist is null when params != 1).
        val values: Collection<Expr.Const> = move.delta.values
        if (values.size != 1) return null
        // Commit moves wrap the sampled value in Hidden; the Dist is keyed by
        // the underlying value, so unwrap before lookup.
        val raw = values.first()
        val sampled = if (raw is Expr.Const.Hidden) raw.inner else raw
        return dist.weight(sampled)
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
    val actionId: NodeId?
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

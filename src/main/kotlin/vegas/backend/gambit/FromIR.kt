/**
 * # Gambit EFG Backend
 *
 * This package converts Vegas ActionDag IR into Gambit's Extensive Form Game (EFG) format.
 *
 * ## Architecture
 *
 * **Pipeline**: `GameIR -> GameTree -> EFG String`
 *
 * 1. **Eval.kt** - Expression evaluation with IrVal runtime values
 * 2. **GameState.kt** - History representation (FrontierAssignmentSlice, History) for perfect recall
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

import vegas.FieldRef
import vegas.Rational
import vegas.RoleId
import vegas.StaticError
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.ActionSpec
import vegas.ir.ActionStruct
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.Visibility

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
 *      each slice is a map from (role, variable) to the IrVal written by some
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
    val gen = EfgGenerator(ir)
    val policy = if (includeAbandonment) EfgGenerator.FULL_EXPANSION else EfgGenerator.FAIR_PLAY
    val frontier = FrontierMachine.from(ir.dag)
    val initialState = History()
    val initialKnowledge: HistoryViews = (ir.roles + ir.chanceRoles).associateWith { History() }
    var tree = gen.exploreFromFrontier(frontier, initialState, initialKnowledge, policy)

    // In order to generate text, prune all Continuation nodes (abandonment branches)
    // In order for this to be an actual game, the continuations MUST NOT cross infosets.
    // This is true for FAIR_PLAY and (vacuously) for FULL_EXPANSION, so we're safe.
    tree = pruneContinuations(tree)

    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from ActionDag",
        strategicPlayers = ir.roles,
        tree = tree
    ).toEfg()
}

/**
 * Remove all Continuation nodes from the tree by mutating Choice.subtree fields.
 *
 * Instead of removing choices, we leverage that Choice.subtree is mutable (var).
 * We filter out choices that lead to Continuations and reconstruct Decision nodes.
 */
private fun pruneContinuations(node: GameTree): GameTree {
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
    // The "Board State" (Outer Loop State)
    val frontier: FrontierMachine<ActionId>,
    val history: History,

    // The "Transaction State" (Inner Loop State)
    val partialFrontierAssignment: FrontierAssignmentSlice,

    // The "Edge Identity" (For Policy / Resume)
    val actionId: ActionId?
)

/**
 * Create a frontier slice where all parameters of the given actions are set to [IrVal.Quit].
 * This represents the "quit" choice where a strategic player opts out of all actions at a frontier.
 */
internal fun allParametersQuit(dag: ActionDag, role: RoleId, actions: List<ActionId>): FrontierAssignmentSlice =
    actions.flatMap { actionId ->
        dag.params(actionId).map { FieldRef(role, it.name) to IrVal.Quit }
    }.toMap()

/**
 * Combine per-action parameter assignments into a unified frontier slice.
 *
 * Takes a list of actions and corresponding assignments (maps from parameter name to value),
 * and combines them into a single frontier slice (map from FieldRef to value).
 *
 * @param roleToActionId Function to look up which role owns an action
 * @param actions List of action IDs in the frontier
 * @param assignments Corresponding parameter assignments for each action
 * @return Unified frontier slice mapping FieldRef -> IrVal
 */
private fun combineAssignmentsIntoFrontier(
    roleToActionId: (ActionId) -> RoleId,
    actions: List<ActionId>,
    assignments: List<Map<VarId, IrVal>>
): FrontierAssignmentSlice {
    val frontierSlice = mutableMapOf<FieldRef, IrVal>()
    actions.zip(assignments).forEach { (actionId, localAssigment) ->
        val role = roleToActionId(actionId)
        localAssigment.forEach { (varId, value) ->
            // If two actions write the same field, last-in-wins; IR should avoid that.
            frontierSlice[FieldRef(role, varId)] = value
        }
    }
    return frontierSlice
}

/**
 * Enumerate all explicit (non-abandonment) joint assignments for a role across all
 * its actions in the current frontier.
 *
 * Returns pairs of (ActionId, FrontierAssignmentSlice) where:
 * - ActionId identifies this as an explicit move (for policy checking)
 * - FrontierAssignmentSlice contains the actual field assignments
 *
 * For joint moves across multiple actions, uses the first ActionId as a marker.
 */
internal fun enumerateRoleFrontierChoices(
    dag: ActionDag,
    role: RoleId,
    actions: List<ActionId>,
    history: History,
    playerKnowledge: History,
): List<Pair<ActionId, FrontierAssignmentSlice>> {
    // ========== Check if Role Has Abandoned ==========
    // Once a role has abandoned (some field Quit), it has no explicit choices anymore.
    if (history.quit(role)) return emptyList()

    // ========== Enumerate Assignments Per Action ==========
    // For each action, enumerate its local assignments.
    val perActionAssignments: List<List<Map<VarId, IrVal>>> =
        actions.map { actionId ->
            enumerateAssignmentsForAction(dag, actionId, history, playerKnowledge)
        }

    if (perActionAssignments.any { it.isEmpty() }) return emptyList()

    // ========== Compute Cartesian Product ==========
    // Cross-product over actions; then flatten into a single FrontierAssignmentSlice.
    val combinations: List<List<Map<VarId, IrVal>>> = cartesian(perActionAssignments)

    // Use first ActionId as a marker for explicit moves (for policy checking)
    val representativeActionId = actions.first()

    return combinations.map { localAssigmentList ->
        val frontierSlice = combineAssignmentsIntoFrontier({ dag.struct(it).owner }, actions, localAssigmentList)
        representativeActionId to frontierSlice
    }
}

/**
 * Enumerate assignments for a single action under the current global history.
 * Commit/reveal semantics:
 *  - COMMIT: pick from type domain, store as Hidden(base).
 *  - REVEAL: if prior value is Hidden(x), then only choice is x (as visible value);
 *            otherwise, no legal choice.
 *  - PUBLIC: pick from type domain, store as visible value.
 *
 * Guards are evaluated with the assignment layered on top of the player's knowledge.
 */
private fun enumerateAssignmentsForAction(
    dag: ActionDag,
    actionId: ActionId,
    history: History,
    playerKnowledge: History,
): List<Map<VarId, IrVal>> {
    val struct: ActionStruct = dag.struct(actionId)
    val spec: ActionSpec = dag.spec(actionId)
    val role = struct.owner

    if (spec.params.isEmpty()) return listOf(emptyMap())
    if (history.quit(role)) return emptyList()

    // ========== Build Domain for Each Parameter ==========
    val lists: List<List<Pair<VarId, IrVal>>> = spec.params.map { param ->
        val fieldRef = FieldRef(role, param.name)
        val prior = history.get(fieldRef)
        val vis = struct.visibility.getValue(fieldRef)

        val baseDomain: List<IrVal> = when (vis) {
            Visibility.REVEAL ->
                when (prior) {
                    is IrVal.Hidden -> listOf(prior.inner)
                    else -> emptyList()
                }

            Visibility.PUBLIC, Visibility.COMMIT ->
                when (param.type) {
                    is Type.BoolType ->
                        listOf(IrVal.BoolVal(true), IrVal.BoolVal(false))

                    is Type.SetType ->
                        param.type.values.sorted().map { v -> IrVal.IntVal(v) }

                    is Type.IntType ->
                        throw StaticError("Cannot enumerate IntType; use SetType or BoolType")
                }
        }

        // The packet we STORE in the frontier must respect visibility (Hidden)
        val domainWithVis: List<IrVal> = when (vis) {
            Visibility.COMMIT -> baseDomain.map { v -> IrVal.Hidden(v) }
            Visibility.PUBLIC, Visibility.REVEAL -> baseDomain
        }

        domainWithVis.map { v -> param.name to v }
    }

    val rawAssignments: List<Map<VarId, IrVal>> =
        cartesian(lists).map { it.toMap() }

    // ========== Filter by Guard Condition ==========
    // Guard: evaluated on player's knowledge with this action's packet overlayed.
    return rawAssignments.filter { localAssigment ->
        // Unwrap Hidden values for the actor's own guard evaluation.
        // The player knows what they are choosing right now.
        val unwrappedPkt = localAssigment.mapValues { (_, v) ->
            if (v is IrVal.Hidden) v.inner else v
        }

        val tempHeap = History(toFrontierMap(role, unwrappedPkt), playerKnowledge)
        eval({ tempHeap.get(it) }, spec.guardExpr).asBool()
    }
}

/**
 * Two-phase EFG generator with spine-and-ribs architecture.
 *
 * Supports two modes:
 * - **Spine generation** (Phase 1): Generate happy-path tree without abandonment branches
 * - **Full generation** (Phase 2): Stitch abandonment branches into spine to create full tree
 *
 * The construction proceeds in two nested loops:
 * - **Frontier loop** ([exploreFromFrontier]): Advances through DAG frontiers sequentially.
 *   Each frontier represents a simultaneous-move round in the game.
 * - **Role loop** ([exploreJointChoices]): Within each frontier, enumerates all possible
 *   joint action combinations by iterating through roles in deterministic order.
 *
 * These two methods are mutually recursive:
 * - When all roles have chosen at a frontier, commit the joint choice and advance to the next frontier
 * - When exploring a frontier, enumerate each role's choices and recurse on the next role
 *
 * The class structure (rather than nested functions) enables this mutual recursion while
 * maintaining [infosetManager] as scoped mutable history that persists across both phases.
 *
 * **Usage**:
 * ```
 * val gen = EfgGenerator(ir)
 * val spine = gen.buildHappyTree()           // Phase 1: O(N^D) tree
 * val full = gen.stitchBails(spine)          // Phase 2: add abandonment branches
 * ```
 */
internal class EfgGenerator(val ir: GameIR) {
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

    /**
     * Manages information set numbering throughout the tree build.
     * Each strategic player's infoset is identified by their redacted knowledge history.
     * Chance nodes receive sequential numbering.
     */
    private val infosetManager = InfosetManager(ir.roles)

    /**
     * Reconstructs all players' views by replaying the global history stack.
     *
     * This is an O(depth * roles) operation, but it allows us to drop 'views'
     * from GeneratorContext, saving significant memory in large trees.
     */
    private fun reconstructViews(globalHistory: History, roles: Set<RoleId>): HistoryViews {
        // 1. Unwind the stack to get slices in chronological order (Root -> Leaf)
        val slices = ArrayDeque<FrontierAssignmentSlice>()
        var curr: History? = globalHistory

        // Assumes History has a 'parent' or 'prev' field and a 'slice' field
        while (curr != null && curr.past != null) {
            slices.addFirst(curr.lastFrontier)
            curr = curr.past
        }

        // 2. Replay history to build views
        // Start with empty history for everyone
        val currentViews = roles.associateWith { History() }.toMutableMap()

        for (slice in slices) {
            for (role in roles) {
                val view = currentViews.getValue(role)
                // Reuse the existing 'redacted' logic used in exploreJointChoices
                currentViews[role] = view with redacted(slice, role)
            }
        }

        return currentViews
    }

    /**
     * Co-inductively expand Continuation nodes in-place based on a new policy.
     *
     * Walks the game tree and selectively expands deferred branches:
     * - If a Continuation's (role, actionId) satisfies the new policy, resume generation
     * - Otherwise, leave it as a Continuation (or replace with a different Continuation under new policy)
     * - Recursively expand newly generated subtrees
     *
     * **Mutation**: This modifies the tree in-place via Choice.subtree (var).
     *
     * **Use case**: Start with FAIR_PLAY tree (no abandonment), then call expand(tree, FULL_EXPANSION)
     * to add abandonment branches on demand.
     *
     * @param node Root of the subtree to expand
     * @param policy Expansion policy determining which Continuations to expand
     */
    fun expand(node: GameTree, policy: ExpansionPolicy = FULL_EXPANSION) {
        when (node) {
            is GameTree.Terminal -> {}
            is GameTree.Continuation -> {} // Root continuation (edge case)
            is GameTree.Decision -> {
                // 1. Capture the role from the PARENT Decision node
                val currentRole = node.owner

                node.choices.forEach { choice ->
                    when (val subtree = choice.subtree) {
                        is GameTree.Continuation -> {
                            val ctx = subtree.context

                            // 2. Use parent's role + context's actionId
                            if (policy.shouldExpand(currentRole, ctx.actionId)) {
                                // Resume generation (requires re-deriving role for context, see below)
                                val expanded = resumeGeneration(ctx, policy)
                                choice.subtree = expanded
                                expand(expanded, policy)
                            }
                        }
                        else -> expand(subtree, policy)
                    }
                }
            }
        }
    }

    /**
     * Resume generation from a suspended Continuation context.
     *
     * Reconstructs the FrontierSetup by:
     * 1. Re-deriving actionsByRole from frontier.enabled()
     * 2. Re-computing legalChoicesByRole (CPU cost to save RAM)
     * 3. Calling exploreJointChoices with the new policy
     *
     * **Tradeoff**: CPU for RAM - recomputation is acceptable since RAM is the bottleneck.
     *
     * @param ctx The GeneratorContext embedded in a Continuation node
     * @param policy The expansion policy to use for resumed generation
     * @return Newly generated game subtree
     */
    private fun resumeGeneration(ctx: GeneratorContext, policy: ExpansionPolicy): GameTree {
        // 1. Reconstruct setup (actions, views, etc.)
        val enabled = ctx.frontier.enabled()
        val actionsByRole = enabled.groupBy { ir.dag.owner(it) }
        val roleOrder = actionsByRole.keys.sortedBy { it.name }

        // 2. Reconstruct views from the global history truth
        val reconstructedViews = reconstructViews(ctx.history, ir.roles + ir.chanceRoles)

        val legalChoicesByRole = actionsByRole.mapValues { (role, actions) ->
            enumerateRoleFrontierChoices(
                ir.dag, role, actions,
                ctx.history,
                reconstructedViews.getValue(role) // Use reconstructed view
            )
        }

        val setup = FrontierSetup(
            ctx.frontier,
            ctx.history,
            reconstructedViews,
            actionsByRole,
            roleOrder,
            legalChoicesByRole
        )

        // 3. Derive next role index.
        // Find the first role in the order that:
        //  a) Has parameters (so it SHOULD be in the map if it acted)
        //  b) Is NOT in the map (so it hasn't acted yet)
        // If a role has no params, we skip it (it's "done" by definition).
        val nextRoleIndex = roleOrder.indexOfFirst { role ->
            val hasParams = actionsByRole[role]?.any { ir.dag.params(it).isNotEmpty() } == true
            val hasActed = ctx.partialFrontierAssignment.keys.any { it.owner == role }

            // We stop at the first role that has work to do
            // but hasn't done it yet.
            hasParams && !hasActed
        }

        // Edge Case: If everyone has acted (or no one has params), index is size (terminal state for loop)
        val effectiveIndex = if (nextRoleIndex == -1) roleOrder.size else nextRoleIndex
        // Resume the role loop where it left off
        return exploreJointChoices(setup, effectiveIndex, ctx.partialFrontierAssignment, policy)
    }

    /**
     * Enumerate all joint action combinations at the current frontier by iterating through roles.
     *
     * This is the **role loop**: for each role in [setup.roleOrder][FrontierSetup.roleOrder],
     * enumerate their legal choices and recurse to the next role. When all roles have chosen
     * (roleIndex == roleOrder.size), commit the joint choice and advance to the next frontier.
     *
     * **Mutual recursion**: This method calls [exploreFromFrontier] when all roles have chosen.
     *
     * @param setup Precomputed frontier context (actions by role, legal choices, etc.)
     * @param roleIndex Index into [setup.roleOrder][FrontierSetup.roleOrder] of current role
     * @param partialFrontierAssignment Accumulated action choices from roles [0, roleIndex)
     * @param policy Expansion policy determining which actions to expand vs defer
     * @return Game subtree rooted at this point
     */
    private fun exploreJointChoices(
        setup: FrontierSetup,
        roleIndex: Int,
        partialFrontierAssignment: FrontierAssignmentSlice,
        policy: ExpansionPolicy
    ): GameTree {
        // ========== Terminal: All Roles Have Chosen ==========
        if (roleIndex == setup.roleOrder.size) {
            // All roles have chosen for this frontier: commit frontier map and advance DAG frontier.
            val newHistory = History(partialFrontierAssignment, setup.history)
            val newKnowledge: HistoryViews =
                setup.views.mapValues { (role, info) ->
                    info with redacted(partialFrontierAssignment, role)
                }

            val nextFrontier = setup.frontier.resolveEnabled()
            return exploreFromFrontier(nextFrontier, newHistory, newKnowledge, policy)
        }

        // ========== Current Role Setup ==========
        val role = setup.roleOrder[roleIndex]
        val isChanceNode = role in ir.chanceRoles

        // History index is a pure function of what this role currently knows.
        val infoset = setup.views.getValue(role)
        val infosetId = infosetManager.getHistoryNumber(role, infoset, isChanceNode)

        val actionsForRole = setup.actionsByRole.getValue(role)
        val allParams = actionsForRole.flatMap { ir.dag.params(it) }

        val explicitMoves: List<Pair<ActionId, FrontierAssignmentSlice>> =
            setup.legalChoicesByRole.getValue(role)

        // ========== Unified Move Enumeration ==========
        // Build unified list of ALL moves (explicit + abandonment), then apply policy to each.
        // Chance nodes only have explicit moves (no abandonment option).
        val abandonmentSlice = if (allParams.isEmpty()) emptyMap()
        else allParametersQuit(ir.dag, role, actionsForRole)

        val allMoves: List<Pair<ActionId?, FrontierAssignmentSlice>> =
            if (isChanceNode) {
                // Chance nodes: only explicit moves (always expand, no policy check)
                explicitMoves
            } else {
                // Strategic nodes: explicit moves + quit
                explicitMoves + (null to abandonmentSlice)
            }

        // ========== Policy-Driven Choice Generation ==========
        // For each move, check policy to decide: expand now or create Continuation?
        val allChoices: List<GameTree.Choice> =
            allMoves.map { (actionId, frontierDelta) ->
                // Chance nodes always expand. Strategic nodes consult the policy.
                val shouldExpand = isChanceNode || policy.shouldExpand(role, actionId)

                val subtree = if (shouldExpand) {
                    // Policy says expand: recurse immediately
                    exploreJointChoices(setup, roleIndex + 1, partialFrontierAssignment + frontierDelta, policy)
                } else {
                    // Policy says defer: create Continuation node with embedded context
                    GameTree.Continuation(
                        GeneratorContext(
                            frontier = setup.frontier,
                            history = setup.history,
                            partialFrontierAssignment = partialFrontierAssignment + frontierDelta,
                            actionId = actionId
                        )
                    )
                }

                GameTree.Choice(
                    action = extractActionLabel(frontierDelta, role),
                    subtree = subtree,
                    probability = if (isChanceNode) Rational(1, allMoves.size) else null
                )
            }

        if (allChoices.isEmpty()) {
            throw StaticError("No choices for role $role at frontier")
        }

        // ========== Handle Structural Frontiers (No-Op) ==========
        // Structural frontier: this role has no parameters at all here.
        // No real decision -> no node; just pick the (unique) subtree.
        if (allParams.isEmpty()) {
            return allChoices.first().subtree
        }

        // ========== Create Decision Node ==========
        return GameTree.Decision(
            owner = role,
            infosetId = infosetId,
            choices = allChoices,
            isChance = isChanceNode
        )
    }

    /**
     * Explore the game tree starting from a given frontier history.
     *
     * This is the **frontier loop**: Process one frontier (simultaneous-move round) by:
     * 1. Checking if we've reached a terminal node (no more frontiers)
     * 2. Grouping enabled actions by role
     * 3. Precomputing legal choices for each role under the current history snapshot
     * 4. Delegating to [exploreJointChoices] to enumerate all joint action combinations
     *
     * **Mutual recursion**: [exploreJointChoices] calls this method when a joint choice is committed.
     *
     * @param frontier Current frontier machine history (enabled actions)
     * @param history Global game history (stack of committed frontier slices)
     * @param views Per-role redacted view of history (for information set construction)
     * @param policy Expansion policy determining which actions to expand vs defer
     * @return Game subtree rooted at this frontier
     */
    internal fun exploreFromFrontier(
        frontier: FrontierMachine<ActionId>,
        history: History,
        views: HistoryViews,
        policy: ExpansionPolicy
    ): GameTree {
        // ========== Check for Terminal Nodes ==========
        if (frontier.isComplete()) {
            val pay = ir.payoffs.mapValues { (_, e) -> eval({ history.get(it) }, e).toOutcome() }
            return GameTree.Terminal(pay)
        }

        val enabled: Set<ActionId> = frontier.enabled()
        require(enabled.isNotEmpty()) {
            "Frontier has no enabled actions but is not complete"
        }

        // ========== Group Actions by Role ==========
        // Actions enabled at this frontier, grouped per role => simultaneous "pseudo-frontier"
        val actionsByRole: Map<RoleId, List<ActionId>> = enabled.groupBy { ir.dag.owner(it) }
        val roleOrder: List<RoleId> = actionsByRole.keys.sortedBy { it.name }

        // ========== Precompute Legal Choices ==========
        // Precompute legal explicit assignments per role under the same snapshot history.
        val legalChoicesByRole: Map<RoleId, List<Pair<ActionId, FrontierAssignmentSlice>>> =
            actionsByRole.mapValues { (role, actions) ->
                enumerateRoleFrontierChoices(ir.dag, role, actions, history, views.getValue(role))
            }

        // ========== Explore All Joint Choices ==========
        val setup = FrontierSetup(
            frontier = frontier,
            history = history,
            views = views,
            actionsByRole = actionsByRole,
            roleOrder = roleOrder,
            legalChoicesByRole = legalChoicesByRole
        )

        return exploreJointChoices(
            setup,
            roleIndex = 0,
            partialFrontierAssignment = emptyMap(),
            policy = policy
        )
    }

    /**
     * Frontier-level context computed once and shared across role iteration.
     *
     * Captures the setup for a single simultaneous-move round:
     * - Which actions are enabled and grouped by which role
     * - What legal choices each role has under the current history snapshot
     * - The frontier machine history, global history, and per-role knowledge
     *
     * This is passed through the role loop to avoid recomputing this information for each role.
     */
    private data class FrontierSetup(
        /** Frontier machine tracking which actions are enabled */
        val frontier: FrontierMachine<ActionId>,
        /** Global game history (stack of frontier slices) */
        val history: History,
        /** Per-role redacted knowledge for information set construction */
        val views: HistoryViews,
        /** Actions enabled at this frontier, grouped by acting role */
        val actionsByRole: Map<RoleId, List<ActionId>>,
        /** Deterministic ordering of roles (alphabetical by name) */
        val roleOrder: List<RoleId>,
        /** Precomputed legal choice combinations for each role (with ActionId for policy checking) */
        val legalChoicesByRole: Map<RoleId, List<Pair<ActionId, FrontierAssignmentSlice>>>,
    )
}

// Label only this role's non-Quit fields.
// Keep Hidden wrapper for commitments so Gambit GUI shows the flow.
private fun extractActionLabel(frontierDelta: FrontierAssignmentSlice, role: RoleId): Map<VarId, IrVal> = frontierDelta
    .filterKeys { fr -> fr.owner == role }
    .filterValues { v -> v != IrVal.Quit }
    .mapKeys { (fr, _) -> fr.param }

private fun <T> cartesian(lists: List<List<T>>): List<List<T>> =
    lists.fold(listOf(emptyList())) { acc, xs ->
        acc.flatMap { a -> xs.map { x -> a + x } }
    }

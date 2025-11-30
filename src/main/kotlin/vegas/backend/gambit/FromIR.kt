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
 * 2. **GameState.kt** - State representation (FrontierSlice, Infoset) for perfect recall
 * 3. **FromIR.kt** - Main algorithm: IR -> GameTree conversion via frontier exploration
 * 4. **Gambit.kt** - Game tree data structure (Decision/Terminal nodes)
 * 5. **ToText.kt** - EFG text format serialization
 *
 * ## Key Concepts
 *
 * - **Frontier-based exploration**: Each frontier becomes a simultaneous-move round
 * - **Perfect recall**: Information sets keyed by complete redacted history (Infoset stack)
 * - **Commit/Reveal**: Information hiding via Hidden -> Opaque transformation
 * - **Epistemic layering**: Each frontier slice represents one layer of observations
 *
 * ## Entry Point
 *
 * ```kotlin
 * generateExtensiveFormGame(ir: GameIR): String
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
 * This replaces the binary GenerationMode enum with a flexible predicate.
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
     * @param role The role making the decision
     * @param action The action being considered (null = bail)
     * @return true to expand immediately, false to create Continuation
     */
    fun shouldExpand(role: RoleId, action: ActionId?): Boolean
}

/**
 * Build a Gambit EFG string from the ActionDag-based IR.
 *
 * Uses policy-driven generation with optional bail branch inclusion.
 *
 * Semantics (informally):
 *
 *  - The ActionDag is a partial order of actions. At runtime, we explore it by
 *    repeatedly taking a *frontier* of currently enabled actions. Each resolved
 *    frontier contributes one "epistemic layer" of writes along a history.
 *
 *  - Global state is represented as a stack of frontier slices:
 *      each slice is a map from (role, variable) to the IrVal written by some
 *      action in that frontier.  The stack order is the order in which frontiers
 *      are resolved along that history.
 *
 *  - Each player maintains a parallel stack of *redacted* slices (a KnowledgeMap):
 *      * their own fields are seen with their actual values;
 *      * other players' committed (hidden) values appear as Quit;
 *      * Quit is used for abandonment ("bail") and is never hidden.
 *
 *  - An information set for a role is keyed purely by that role's redacted stack.
 *    This yields perfect recall in the usual extensive-form sense: the role can
 *    always recover what it has previously done and observed.
 *
 *  - Each resolved frontier is treated as a simultaneous-move round:
 *      * all actions enabled in that frontier execute exactly once per history;
 *      * for each role we enumerate joint packets for all of its actions in that
 *        frontier (subject to guards);
 *      * after all roles choose, the resulting frontier slice is pushed onto the
 *        global state and all players' knowledge stacks.
 *
 * This layering is epistemic, not part of the IR itself: it is induced by the
 * frontier exploration of the ActionDag and respects its causal partial order.
 */
fun generateExtensiveFormGame(ir: GameIR, happyOnly: Boolean = false): String {
    val gen = EfgGenerator(ir)
    val policy = if (happyOnly) EfgGenerator.FAIR_PLAY else EfgGenerator.FULL_EXPANSION
    val frontier = FrontierMachine.from(ir.dag)
    val initialState = Infoset()
    val initialKnowledge: KnowledgeMap = (ir.roles + ir.chanceRoles).associateWith { Infoset() }
    var tree = gen.exploreFromFrontier(frontier, initialState, initialKnowledge, policy)

    // For happyOnly mode, prune all Continuation nodes (bail branches)
    // to maintain backward compatibility with old SPINE_ONLY behavior
    if (happyOnly) {
        tree = pruneContinuations(tree)
    }

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
 * This is used for backward compatibility with `happyOnly=true` mode,
 * which produces a tree with NO bail branches (not even as Continuations).
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
 * This is mutable state intended to be scoped to a single game tree build.
 *
 * @param roles Set of strategic player role IDs (chance roles excluded)
 */
private class InfosetManager(roles: Set<RoleId>) {
    private val perRole: Map<RoleId, MutableMap<Infoset, Int>> = roles.associateWith { mutableMapOf() }

    private var chanceCounter: Int = 0

    fun getInfosetNumber(role: RoleId, key: Infoset, isChance: Boolean): Int {
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
 *
 * Memory cost: O(depth) for Infoset stacks + O(1) for other fields.
 * Recomputation cost: Re-deriving legal choices is CPU-intensive but saves RAM.
 *
 * Tradeoff: CPU for RAM (acceptable since RAM is the bottleneck for large trees).
 */
internal data class GeneratorContext(
    // Minimal state to reconstruct FrontierSetup
    val frontier: FrontierMachine<ActionId>,
    val state: State,                        // Infoset stack (grows with depth)
    val knowledgeMap: KnowledgeMap,          // |Players| Infoset stacks

    // Position in role iteration loop
    val roleIndex: Int,
    val jointChoices: FrontierSlice,

    // Metadata for policy re-evaluation during expand()
    val role: RoleId,          // Which role is deciding at this point
    val actionId: ActionId?    // Which action led to this continuation (null = bail)
)

/**
 * Create a frontier slice where all parameters of the given actions are set to [IrVal.Quit].
 * This represents the "bail" choice where a strategic player opts out of all actions at a frontier.
 */
private fun allParametersQuit(dag: ActionDag, role: RoleId, actions: List<ActionId>): FrontierSlice =
    actions.flatMap { actionId ->
        dag.params(actionId).map { FieldRef(role, it.name) to IrVal.Quit }
    }.toMap()

/**
 * Combine per-action parameter packets into a unified frontier slice.
 *
 * Takes a list of actions and corresponding packets (maps from parameter name to value),
 * and combines them into a single frontier slice (map from FieldRef to value).
 *
 * @param roleToActionId Function to look up which role owns an action
 * @param actions List of action IDs in the frontier
 * @param packets Corresponding parameter assignments for each action
 * @return Unified frontier slice mapping FieldRef -> IrVal
 */
private fun combinePacketsIntoFrontier(
    roleToActionId: (ActionId) -> RoleId,
    actions: List<ActionId>,
    packets: List<Map<VarId, IrVal>>
): FrontierSlice {
    val frontierSlice = mutableMapOf<FieldRef, IrVal>()
    actions.zip(packets).forEach { (actionId, pkt) ->
        val role = roleToActionId(actionId)
        pkt.forEach { (varId, value) ->
            // If two actions write the same field, last-in-wins; IR should avoid that.
            frontierSlice[FieldRef(role, varId)] = value
        }
    }
    return frontierSlice
}

/**
 * Enumerate all explicit (non-bail) joint packets for a role across all
 * its actions in the current frontier.
 *
 * Returns pairs of (ActionId, FrontierSlice) where:
 * - ActionId identifies this as an explicit move (for policy checking)
 * - FrontierSlice contains the actual field assignments
 *
 * For joint moves across multiple actions, uses the first ActionId as a marker.
 */
private fun enumerateRoleFrontierChoices(
    dag: ActionDag,
    role: RoleId,
    actions: List<ActionId>,
    state: State,
    playerKnowledge: Infoset,
): List<Pair<ActionId, FrontierSlice>> {
    // ========== Check if Role Has Bailed ==========
    // Once a role has bailed (some field Quit), it has no explicit choices anymore.
    if (state.quit(role)) return emptyList()

    if (actions.isEmpty()) {
        // Structural frontier: no parameters, but still an explicit (non-bail) choice
        // Use a synthetic marker - actions[0] would fail here, so we need to handle this
        // Actually, if actions.isEmpty(), we shouldn't have an ActionId to use
        // Return empty list - structural frontiers will be handled specially
        return emptyList()
    }

    // ========== Enumerate Packets Per Action ==========
    // For each action, enumerate its local packets.
    val perActionPackets: List<List<Map<VarId, IrVal>>> =
        actions.map { actionId ->
            enumeratePacketsForAction(dag, actionId, state, playerKnowledge)
        }

    if (perActionPackets.any { it.isEmpty() }) return emptyList()

    // ========== Compute Cartesian Product ==========
    // Cross-product over actions; then flatten into a single FrontierSlice.
    val combinations: List<List<Map<VarId, IrVal>>> = cartesian(perActionPackets)

    // Use first ActionId as a marker for explicit moves (for policy checking)
    val representativeActionId = actions.first()

    return combinations.map { pktList ->
        val frontierSlice = combinePacketsIntoFrontier({ dag.struct(it).role }, actions, pktList)
        representativeActionId to frontierSlice
    }
}

/**
 * Enumerate packets for a single action under the current global state.
 * Commit/reveal semantics:
 *  - COMMIT: pick from type domain, store as Hidden(base).
 *  - REVEAL: if prior value is Hidden(x), then only choice is x (as visible value);
 *            otherwise, no legal choice.
 *  - PUBLIC: pick from type domain, store as visible value.
 *
 * Guards are evaluated with the packet layered on top of the player's knowledge.
 */
private fun enumeratePacketsForAction(
    dag: ActionDag,
    actionId: ActionId,
    state: State,
    playerKnowledge: Infoset,
): List<Map<VarId, IrVal>> {
    val struct: ActionStruct = dag.struct(actionId)
    val spec: ActionSpec = dag.spec(actionId)
    val role = struct.role

    if (spec.params.isEmpty()) return listOf(emptyMap())
    if (state.quit(role)) return emptyList()

    // ========== Build Domain for Each Parameter ==========
    val lists: List<List<Pair<VarId, IrVal>>> = spec.params.map { param ->
        val fieldRef = FieldRef(role, param.name)
        val prior = state.get(fieldRef)
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

    val rawPackets: List<Map<VarId, IrVal>> =
        cartesian(lists).map { it.toMap() }

    // ========== Filter by Guard Condition ==========
    // Guard: evaluated on player's knowledge with this action's packet overlayed.
    return rawPackets.filter { pkt ->
        // Unwrap Hidden values for the actor's own guard evaluation.
        // The player knows what they are choosing right now.
        val unwrappedPkt = pkt.mapValues { (_, v) ->
            if (v is IrVal.Hidden) v.inner else v
        }

        val tempHeap = Infoset(toFrontierMap(role, unwrappedPkt), playerKnowledge)
        eval({ tempHeap.get(it) }, spec.guardExpr).asBool()
    }
}

/**
 * Two-phase EFG generator with spine-and-ribs architecture.
 *
 * Supports two modes:
 * - **Spine generation** (Phase 1): Generate happy-path tree without bail branches
 * - **Full generation** (Phase 2): Stitch bail branches into spine to create full tree
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
 * maintaining [infosetManager] as scoped mutable state that persists across both phases.
 *
 * **Usage**:
 * ```
 * val gen = EfgGenerator(ir)
 * val spine = gen.buildHappyTree()           // Phase 1: O(N^D) tree
 * val full = gen.stitchBails(spine)          // Phase 2: add bail branches
 * ```
 */
internal class EfgGenerator(val ir: GameIR) {
    companion object {
        /**
         * FAIR_PLAY: Expand all explicit moves, defer bail branches.
         *
         * This is the default policy and produces the "spine" tree:
         * - Focuses on strategic play where players actively participate
         * - Bail branches can be added later via expand()
         * - Equivalent to old SPINE_ONLY mode
         */
        val FAIR_PLAY: ExpansionPolicy = ExpansionPolicy { _, action -> action != null }

        /**
         * FULL_EXPANSION: Expand everything including bail branches.
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
     * Co-inductively expand Continuation nodes in-place based on a new policy.
     *
     * Walks the game tree and selectively hydrates deferred branches:
     * - If a Continuation's (role, actionId) satisfies the new policy, resume generation
     * - Otherwise, leave it as a Continuation (or replace with a different Continuation under new policy)
     * - Recursively expand newly generated subtrees
     *
     * **Mutation**: This modifies the tree in-place via Choice.subtree (var).
     *
     * **Use case**: Start with FAIR_PLAY tree (no bail), then call expand(tree, FULL_EXPANSION)
     * to add bail branches on demand.
     *
     * @param node Root of the subtree to expand
     * @param policy Expansion policy determining which Continuations to hydrate
     */
    fun expand(node: GameTree, policy: ExpansionPolicy = FULL_EXPANSION) {
        when (node) {
            is GameTree.Terminal -> {
                // Terminal nodes have no children to expand
            }

            is GameTree.Continuation -> {
                // Standalone Continuation at root should not happen in well-formed trees
                // (would mean the initial call deferred the very first decision)
                // Do nothing - caller should handle this edge case
            }

            is GameTree.Decision -> {
                node.choices.forEach { choice ->
                    when (val subtree = choice.subtree) {
                        is GameTree.Continuation -> {
                            val ctx = subtree.context
                            // Check if the new policy wants to expand this deferred action
                            if (policy.shouldExpand(ctx.role, ctx.actionId)) {
                                // Hydrate in-place (MUTATION)
                                val expanded = resumeGeneration(ctx, policy)
                                choice.subtree = expanded
                                // Recursively expand the newly generated subtree
                                expand(expanded, policy)
                            }
                            // else: Leave as Continuation (still out of policy)
                        }
                        else -> {
                            // Recurse into existing Decision/Terminal nodes
                            expand(subtree, policy)
                        }
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
        // Reconstruct frontier setup from stored context
        val enabled = ctx.frontier.enabled()
        val actionsByRole = enabled.groupBy { ir.dag.owner(it) }
        val roleOrder = actionsByRole.keys.sortedBy { it.name }
        val legalChoicesByRole = actionsByRole.mapValues { (role, actions) ->
            enumerateRoleFrontierChoices(
                ir.dag, role, actions,
                ctx.state, ctx.knowledgeMap.getValue(role)
            )
        }

        val setup = FrontierSetup(
            ctx.frontier, ctx.state, ctx.knowledgeMap,
            actionsByRole, roleOrder, legalChoicesByRole
        )

        // Resume the role loop where it left off
        return exploreJointChoices(setup, ctx.roleIndex, ctx.jointChoices, policy)
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
     * @param jointChoices Accumulated action choices from roles [0, roleIndex)
     * @param policy Expansion policy determining which actions to expand vs defer
     * @return Game subtree rooted at this point
     */
    private fun exploreJointChoices(
        setup: FrontierSetup,
        roleIndex: Int,
        jointChoices: FrontierSlice,
        policy: ExpansionPolicy
    ): GameTree {
        // ========== Terminal: All Roles Have Chosen ==========
        if (roleIndex == setup.roleOrder.size) {
            // All roles have chosen for this frontier: commit frontier map and advance DAG frontier.
            val newState = Infoset(jointChoices, setup.state)
            val newKnowledge: KnowledgeMap =
                setup.knowledgeMap.mapValues { (role, info) ->
                    info with redacted(jointChoices, role)
                }

            val nextFrontier = setup.frontier.resolveEnabled()
            return exploreFromFrontier(nextFrontier, newState, newKnowledge, policy)
        }

        // ========== Current Role Setup ==========
        val role = setup.roleOrder[roleIndex]
        val isChanceNode = role in ir.chanceRoles

        // Infoset index is a pure function of what this role currently knows.
        val infoset = setup.knowledgeMap.getValue(role)
        val infosetId = infosetManager.getInfosetNumber(role, infoset, isChanceNode)

        val actionsForRole = setup.actionsByRole.getValue(role)
        val allParams = actionsForRole.flatMap { ir.dag.params(it) }

        val explicitMoves: List<Pair<ActionId, FrontierSlice>> =
            setup.legalChoicesByRole.getValue(role)

        // ========== Unified Move Enumeration ==========
        // Build unified list of ALL moves (explicit + bail), then apply policy to each.
        // Chance nodes only have explicit moves (no bail option).
        val bailFrontier = if (allParams.isEmpty()) emptyMap()
                          else allParametersQuit(ir.dag, role, actionsForRole)

        val allMoves: List<Pair<ActionId?, FrontierSlice>> =
            if (isChanceNode) {
                // Chance nodes: only explicit moves (always expand, no policy check)
                explicitMoves
            } else {
                // Strategic nodes: explicit moves + bail move
                explicitMoves + (null to bailFrontier)
            }

        // ========== Policy-Driven Choice Generation ==========
        // For each move, check policy to decide: expand now or create Continuation?
        val allChoices: List<GameTree.Choice> =
            allMoves.map { (actionId, frontierDelta) ->
                // Chance nodes always expand. Strategic nodes consult the policy.
                val shouldExpand = isChanceNode || policy.shouldExpand(role, actionId)

                val subtree = if (shouldExpand) {
                    // Policy says expand: recurse immediately
                    exploreJointChoices(setup, roleIndex + 1, jointChoices + frontierDelta, policy)
                } else {
                    // Policy says defer: create Continuation node with embedded context
                    GameTree.Continuation(
                        GeneratorContext(
                            frontier = setup.frontier,
                            state = setup.state,
                            knowledgeMap = setup.knowledgeMap,
                            roleIndex = roleIndex + 1,
                            jointChoices = jointChoices + frontierDelta,
                            role = role,
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
     * Explore the game tree starting from a given frontier state.
     *
     * This is the **frontier loop**: Process one frontier (simultaneous-move round) by:
     * 1. Checking if we've reached a terminal node (no more frontiers)
     * 2. Grouping enabled actions by role
     * 3. Precomputing legal choices for each role under the current state snapshot
     * 4. Delegating to [exploreJointChoices] to enumerate all joint action combinations
     *
     * **Mutual recursion**: [exploreJointChoices] calls this method when a joint choice is committed.
     *
     * @param frontier Current frontier machine state (enabled actions)
     * @param state Global game state (stack of committed frontier slices)
     * @param knowledgeMap Per-role redacted view of state (for information set construction)
     * @param policy Expansion policy determining which actions to expand vs defer
     * @return Game subtree rooted at this frontier
     */
    internal fun exploreFromFrontier(
        frontier: FrontierMachine<ActionId>,
        state: State,
        knowledgeMap: KnowledgeMap,
        policy: ExpansionPolicy
    ): GameTree {
        // ========== Check for Terminal Nodes ==========
        if (frontier.isComplete()) {
            val pay = ir.payoffs.mapValues { (_, e) -> eval({ state.get(it) }, e).toOutcome() }
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
        // Precompute legal explicit packets per role under the same snapshot state.
        val legalChoicesByRole: Map<RoleId, List<Pair<ActionId, FrontierSlice>>> =
            actionsByRole.mapValues { (role, actions) ->
                enumerateRoleFrontierChoices(ir.dag, role, actions, state, knowledgeMap.getValue(role))
            }

        // ========== Explore All Joint Choices ==========
        val setup = FrontierSetup(
            frontier = frontier,
            state = state,
            knowledgeMap = knowledgeMap,
            actionsByRole = actionsByRole,
            roleOrder = roleOrder,
            legalChoicesByRole = legalChoicesByRole
        )

        return exploreJointChoices(
            setup,
            roleIndex = 0,
            jointChoices = emptyMap(),
            policy = policy
        )
    }

    /**
     * Frontier-level context computed once and shared across role iteration.
     *
     * Captures the setup for a single simultaneous-move round:
     * - Which actions are enabled and grouped by which role
     * - What legal choices each role has under the current state snapshot
     * - The frontier machine state, global state, and per-role knowledge
     *
     * This is passed through the role loop to avoid recomputing this information for each role.
     */
    private data class FrontierSetup(
        /** Frontier machine tracking which actions are enabled */
        val frontier: FrontierMachine<ActionId>,
        /** Global game state (stack of frontier slices) */
        val state: State,
        /** Per-role redacted knowledge for information set construction */
        val knowledgeMap: KnowledgeMap,
        /** Actions enabled at this frontier, grouped by acting role */
        val actionsByRole: Map<RoleId, List<ActionId>>,
        /** Deterministic ordering of roles (alphabetical by name) */
        val roleOrder: List<RoleId>,
        /** Precomputed legal choice combinations for each role (with ActionId for policy checking) */
        val legalChoicesByRole: Map<RoleId, List<Pair<ActionId, FrontierSlice>>>,
    )
}

// Label only this role's non-Quit fields.
// Keep Hidden wrapper for commitments so Gambit GUI shows the flow.
private fun extractActionLabel(frontierDelta: FrontierSlice, role: RoleId): Map<VarId, IrVal> = frontierDelta
    .filterKeys { fr -> fr.role == role }
    .filterValues { v -> v != IrVal.Quit }
    .mapKeys { (fr, _) -> fr.param }

private fun <T> cartesian(lists: List<List<T>>): List<List<T>> =
    lists.fold(listOf(emptyList())) { acc, xs ->
        acc.flatMap { a -> xs.map { x -> a + x } }
    }

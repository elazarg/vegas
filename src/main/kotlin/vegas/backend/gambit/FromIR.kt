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
 * Build a Gambit EFG string from the ActionDag-based IR.
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
 *        global state and all players’ knowledge stacks.
 *
 * This layering is epistemic, not part of the IR itself: it is induced by the
 * frontier exploration of the ActionDag and respects its causal partial order.
 */
fun generateExtensiveFormGame(ir: GameIR): String {
    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from ActionDag",
        strategicPlayers = ir.roles,
        tree = GameTreeBuilder.build(ir)
    ).toEfg()
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
 * its actions in the current frontier, as a list of FrontierSlice deltas.
 */
private fun enumerateRoleFrontierChoices(
    dag: ActionDag,
    role: RoleId,
    actions: List<ActionId>,
    state: State,
    playerKnowledge: Infoset,
): List<FrontierSlice> {
    // ========== Check if Role Has Bailed ==========
    // Once a role has bailed (some field Quit), it has no explicit choices anymore.
    if (state.quit(role)) return emptyList()

    if (actions.isEmpty()) return listOf(emptyMap())

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

    return combinations.map { pktList ->
        combinePacketsIntoFrontier({ dag.struct(it).role }, actions, pktList)
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
 * Builds an extensive-form game tree from ActionDag IR via frontier exploration.
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
 * maintaining [infosetManager] as scoped mutable state local to the tree build.
 *
 * **Usage**: Call [build] to construct a game tree:
 * ```
 * val tree = GameTreeBuilder.build(ir)
 * ```
 */
private class GameTreeBuilder private constructor(val ir: GameIR) {
    /**
     * Manages information set numbering throughout the tree build.
     * Each strategic player's infoset is identified by their redacted knowledge history.
     * Chance nodes receive sequential numbering.
     */
    val infosetManager = InfosetManager(ir.roles)

    companion object {
        /**
         * Build an extensive-form game tree from ActionDag IR.
         *
         * @param ir The game intermediate representation containing the action DAG and payoffs
         * @return The root of the game tree
         */
        fun build(ir: GameIR): GameTree {
            val frontier = FrontierMachine.from(ir.dag)
            val initialState = Infoset()
            val initialKnowledge: KnowledgeMap =
                (ir.roles + ir.chanceRoles).associateWith { Infoset() }
            return GameTreeBuilder(ir).exploreFromFrontier(frontier, initialState, initialKnowledge)
        }
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
     * @return Game subtree rooted at this point
     */
    private fun exploreJointChoices(
        setup: FrontierSetup,
        roleIndex: Int,
        jointChoices: FrontierSlice
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
            return exploreFromFrontier(nextFrontier, newState, newKnowledge)
        }

        // ========== Current Role Setup ==========
        val role = setup.roleOrder[roleIndex]
        val isChanceNode = role in ir.chanceRoles

        // Infoset index is a pure function of what this role currently knows.
        val infoset = setup.knowledgeMap.getValue(role)
        val infosetId = infosetManager.getInfosetNumber(role, infoset, isChanceNode)

        val actionsForRole = setup.actionsByRole.getValue(role)
        val allParams = actionsForRole.flatMap { ir.dag.params(it) }

        val explicitFrontierChoices: List<FrontierSlice> =
            setup.legalChoicesByRole.getValue(role)

        // ========== Build Explicit Choices ==========
        // 1. Explicit choices (non-bail).
        val explicitChoices: List<GameTree.Choice> =
            explicitFrontierChoices.map { frontierDelta ->
                val subtree = exploreJointChoices(setup, roleIndex + 1, jointChoices + frontierDelta)
                GameTree.Choice(
                    action = extractActionLabel(frontierDelta, role),
                    subtree = subtree,
                    probability = null,
                )
            }

        // ========== Apply Probabilities for Chance Nodes ==========
        val explicitWithProb =
            if (isChanceNode)
                explicitChoices.map {
                    it.copy(probability = Rational(1, explicitChoices.size))
                }
            else
                explicitChoices

        // ========== Add Bail Choice for Strategic Roles ==========
        // 2. Bail choice for strategic roles (None on all params).
        val allChoices: List<GameTree.Choice> =
            if (isChanceNode) {
                explicitWithProb
            } else {
                val bailFrontier =
                    if (allParams.isEmpty()) emptyMap()
                    else allParametersQuit(ir.dag, role, actionsForRole)

                val bailChoice = GameTree.Choice(
                    action = emptyMap(), // shows as "Quit" / unlabeled move
                    subtree = exploreJointChoices(setup, roleIndex + 1, jointChoices + bailFrontier),
                    probability = null,
                )

                explicitWithProb + bailChoice
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
            isChance = isChanceNode,
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
     * @return Game subtree rooted at this frontier
     */
    private fun exploreFromFrontier(
        frontier: FrontierMachine<ActionId>,
        state: State,
        knowledgeMap: KnowledgeMap,
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
        val legalChoicesByRole: Map<RoleId, List<FrontierSlice>> =
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

        return exploreJointChoices(setup, roleIndex = 0, jointChoices = emptyMap())
    }

    /**
     * Frontier-level context computed once and shared across role iteration.
     *
     * Captures the setup for a single simultaneous-move round:
     * - Which actions are enabled and grouped by which role
     * - What legal choices each role has under the current state snapshot
     * - The frontier machine state, global state, and per-role knowledge
     *
     * This is passed through the role loop ([GameTreeBuilder.exploreJointChoices]) to avoid
     * recomputing this information for each role.
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
        /** Precomputed legal choice combinations for each role */
        val legalChoicesByRole: Map<RoleId, List<FrontierSlice>>,
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

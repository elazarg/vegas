package vegas.backend.gambit

import vegas.FieldRef
import vegas.RoleId
import vegas.StaticError
import vegas.VarId
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.ActionSpec
import vegas.ir.ActionStruct
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.Visibility

/**
 * Game semantics as a labelled transition system.
 *
 * Provides the operational semantics independent of tree generation:
 * - [enabledMoves]: Enumerate all legal moves at a configuration
 * - [canFinalizeFrontier]: Check if τ (frontier finalization) is enabled
 *
 * Tree generation is a separate concern (unrolling this LTS via TreeUnroller).
 *
 * **Invariant:**
 * This is the single source of truth for "what moves are legal?"
 * All move enumeration logic lives here; TreeUnroller just interprets labels.
 */
internal class GameSemantics(val ir: GameIR) {

    /**
     * Compute all legal moves at a configuration.
     *
     * Returns moves in deterministic order:
     * 1. Explicit moves for each role (in canonical role order)
     * 2. Quit moves for strategic roles (in canonical role order)
     * 3. FinalizeFrontier (if enabled)
     *
     * **Canonical role order:** Roles sorted alphabetically by name.
     * This ensures deterministic tree generation.
     *
     * **Note:** Only generate moves for roles that haven't
     * acted yet in this frontier. A role that has already acted (has fields in
     * config.partial) gets no more moves until the frontier commits.
     *
     * @param config The current configuration
     * @return List of all enabled move labels
     */
    fun enabledMoves(config: Configuration): List<Label> {
        // 1. Terminal condition
        if (config.isTerminal()) return emptyList()

        val moves = mutableListOf<Label>()
        val allRoles = ir.roles + ir.chanceRoles
        val views = config.views(allRoles)
        val actionsByRole = config.actionsByRole(ir.dag)

        // Canonical role order for deterministic tree generation
        val rolesInOrder = actionsByRole.keys.sortedBy { it.name }

        // 2. Explicit moves per role
        // Only generate moves for roles that haven't acted yet
        for (role in rolesInOrder) {
            // Skip roles that already acted in this frontier
            if (config.hasActed(role)) continue

            val actions = actionsByRole.getValue(role)

            // If params_r is empty, r has no move in this frontier
            val allParams = actions.flatMap { ir.dag.params(it) }
            if (allParams.isEmpty()) continue

            val playerView = views.getValue(role)

            // Enumerate all valid field assignments for this role's actions
            val explicitMoves = enumerateRoleFrontierChoices(
                ir.dag, role, actions, config.history, playerView
            )

            moves.addAll(explicitMoves.map { (actionId, delta) ->
                Label.Play(role, delta, PlayTag.Action(actionId))
            })
        }

        // 3. Quit moves for strategic players only.
        // Only generate quit for roles that haven't acted yet
        for (role in ir.roles.sortedBy { it.name }) {  // canonical order
            // Skip roles that already acted in this frontier
            if (config.hasActed(role)) continue

            val actions = actionsByRole[role] ?: continue
            val allParams = actions.flatMap { ir.dag.params(it) }

            if (allParams.isNotEmpty()) {
                val quitDelta = allParametersQuit(ir.dag, role, actions)
                moves.add(Label.Play(role, quitDelta, PlayTag.Quit))
            }
        }

        // 4. FinalizeFrontier step
        if (canFinalizeFrontier(config)) {
            moves.add(Label.FinalizeFrontier)
        }

        return moves
    }

    /**
     * Check if the FinalizeFrontier (τ) step is enabled.
     *
     * Enabled when all roles with parameters have acted:
     * - Done_Γ = MustAct_Γ (roles with params that haven't quit = roles that have acted)
     * - Frontier is not complete (more actions remain)
     *
     * @param config The current configuration
     * @return true if FinalizeFrontier is enabled, false otherwise
     */
    fun canFinalizeFrontier(config: Configuration): Boolean {
        if (config.isTerminal()) return false

        val rolesWithParams = config.rolesWithParams(ir.dag)
        val mustAct = rolesWithParams.filterNot { config.history.quit(it) }
        val done = mustAct.filter { config.hasActed(it) }

        return done.toSet() == mustAct.toSet()
    }
}

/**
 * Apply a move label to get the next configuration.
 *
 * Transition relation:
 * - Play(r, δ, tag): Merge δ into partial frontier (disjoint union)
 * - FinalizeFrontier: Commit partial to history and advance frontier
 *
 * The no-overlapping-writes invariant ensures partial.keys ∩ delta.keys = ∅,
 * so `partial + delta` is a proper disjoint union.
 *
 * @param config The current configuration
 * @param label The move to apply
 * @return The next configuration
 */
internal fun applyMove(config: Configuration, label: Label): Configuration {
    return when (label) {
        is Label.Play -> {
            // next configuration is (frontier, history, partial ⊎ delta)
            // The no-overlapping-writes invariant ensures partial.keys and delta.keys are disjoint
            Configuration(
                frontier = config.frontier,
                history = config.history,
                partial = config.partial + label.delta  // disjoint union
            )
        }

        is Label.FinalizeFrontier -> {
            // next configuration is (frontier.resolveEnabled(), pushSlice(history, partial), ∅)
            // Use existing `History.with` infix operator from GameState.kt
            Configuration(
                frontier = config.frontier.resolveEnabled(),
                history = config.history with config.partial,
                partial = emptyMap()
            )
        }
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
    val spec: ActionSpec = dag.spec(actionId)
    val role = dag.owner(actionId)

    if (spec.params.isEmpty()) return listOf(emptyMap())
    if (history.quit(role)) return emptyList()

    // ========== Build Domain for Each Parameter ==========
    val lists: List<List<Pair<VarId, IrVal>>> = spec.params.map { param ->
        val fieldRef = FieldRef(role, param.name)
        val prior = history.get(fieldRef)
        val vis = dag.visibilityOf(actionId).getValue(fieldRef)

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
        val frontierSlice = combineAssignmentsIntoFrontier({ dag.owner(it) }, actions, localAssigmentList)
        representativeActionId to frontierSlice
    }
}

private fun <T> cartesian(lists: List<List<T>>): List<List<T>> =
    lists.fold(listOf(emptyList())) { acc, xs ->
        acc.flatMap { a -> xs.map { x -> a + x } }
    }

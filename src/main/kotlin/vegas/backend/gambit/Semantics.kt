package vegas.backend.gambit

import vegas.ir.GameIR

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
internal fun GameSemantics.applyMove(config: Configuration, label: Label): Configuration {
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

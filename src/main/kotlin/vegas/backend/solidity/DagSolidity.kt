package vegas.backend.solidity

import vegas.RoleId
import vegas.FieldRef
import vegas.ir.*

/**
 * DAG-based Solidity backend.
 * Generates contracts using action dependencies instead of phase barriers.
 */

/**
 * Linearize ActionDag to assign sequential integer IDs to actions.
 * Sort by (phase index, role name) for deterministic ordering.
 */
fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.nodes
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()

/**
 * Generate action constant name (e.g., "ACTION_Alice_0")
 */
fun actionConstName(role: RoleId, phase: Int): String =
    "ACTION_${role.name}_$phase"

/**
 * Generate action function name (e.g., "move_Alice_0")
 */
fun actionFuncName(role: RoleId, phase: Int): String =
    "move_${role.name}_$phase"

/**
 * Main entry: Generate Solidity from IR using ActionDag.
 * Ensures IR-DAG alignment by expanding commit-reveal first,
 * then building the DAG from the same expanded IR.
 */
fun genSolidityFromDag(orig: GameIR): String {
    val g = expandCommitReveal(orig)           // 1) normalize IR first
    val dag = buildActionDag(g)                // 2) build DAG from same IR
        ?: error("Invalid dependency structure")
    val solAst = irToDagSolidity(g, dag)       // 3) use g + dag consistently
    return renderSolidityContract(solAst)
}

/**
 * Translate IR + ActionDag to SolidityContract AST.
 */
fun irToDagSolidity(g: GameIR, dag: ActionDag): SolidityContract {
    val linearization = linearizeDag(dag)
    val history = ParamHistory(g)

    // Constructor: set lastTs = block.timestamp
    val ctor = Constructor(
        body = listOf(
            Statement.Assign(
                lhs = SolExpr.Var(LAST_TS_VAR),
                rhs = SolExpr.Member(SolExpr.Var("block"), "timestamp")
            )
        )
    )

    // Role enum (None + all roles)
    val roleEnum = EnumDecl(
        name = ROLE_ENUM,
        values = (listOf(NO_ROLE) + g.roles + g.chanceRoles).map { it.name }
    )

    // Storage (no phase variable, add actionDone mapping)
    val storage = buildDagGameStorage(g, dag, linearization)

    // Modifiers (depends, notDone, by, at_final_phase)
    val modifiers = buildDagModifiers(linearization.size)

    // Functions (per-action + payoff + withdraw)
    val functions = buildList {
        // Per-action functions
        addAll(buildActionFunctions(g, dag, linearization, history))

        // Payoff distribution
        add(buildDagPayoffFunction(g, history, linearization.size))

        // Withdraw
        add(buildWithdraw())
    }

    // Events (keep for compatibility, though less meaningful without phases)
    val events = emptyList<EventDecl>() // Could generate per-action events if needed

    // Fallback (reject stray ETH)
    val fallback = FallbackDecl(
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.PAYABLE,
        body = listOf(Statement.Revert("direct ETH not allowed"))
    )

    return SolidityContract(
        name = g.name,
        constructor = ctor,
        enums = listOf(roleEnum),
        storage = storage,
        modifiers = modifiers,
        functions = functions,
        events = events,
        fallback = fallback
    )
}

/**
 * Build storage for DAG-based contract.
 * No phase variable, but add actionDone and actionTimestamp mappings.
 */
private fun buildDagGameStorage(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): List<StorageDecl> = buildList {
    // Timing (no phase variable!)
    add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, LAST_TS_VAR))

    // Action tracking
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Uint256, SolType.Bool),
            visibility = Visibility.PUBLIC,
            name = "actionDone"
        )
    )
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Uint256, SolType.Uint256),
            visibility = Visibility.PUBLIC,
            name = "actionTimestamp"
        )
    )

    // Action constants
    linearization.forEach { (actionId, idx) ->
        val (role, phase) = actionId
        add(
            StorageDecl(
                type = SolType.Uint256,
                visibility = Visibility.PUBLIC,
                name = actionConstName(role, phase),
                constant = true,
                value = SolExpr.IntLit(idx)
            )
        )
    }

    // Roles and balances
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Address, SolType.EnumType(ROLE_ENUM)),
            visibility = Visibility.PUBLIC,
            name = ROLE_MAPPING
        )
    )
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Address, SolType.Int256),
            visibility = Visibility.PUBLIC,
            name = BALANCE_MAPPING
        )
    )

    // Player addresses
    g.roles.forEach { role ->
        add(StorageDecl(SolType.Address, Visibility.PUBLIC, roleAddr(role)))
    }
    g.chanceRoles.forEach { role ->
        add(StorageDecl(SolType.Address, Visibility.PUBLIC, roleAddr(role)))
    }

    // Payoff distribution flag
    add(StorageDecl(SolType.Bool, Visibility.PUBLIC, "payoffs_distributed"))

    // Game state storage (same as phase-based: per-field storage)
    val definedFields = mutableSetOf<FieldRef>()
    g.phases.forEachIndexed { phaseIdx, phase ->
        phase.actions.forEach { (role, sig) ->
            // Per-role "joined" flag
            if (sig.join != null) {
                add(StorageDecl(SolType.Bool, Visibility.PUBLIC, roleDone(role)))
            }
            // Per-parameter storage
            sig.parameters.forEach { p ->
                val field = FieldRef(role, p.name)
                if (!definedFields.contains(field)) {
                    if (!p.visible) {
                        add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, storageParam(role, p.name, true)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, true)))
                        add(StorageDecl(translateType(p.type), Visibility.PUBLIC, storageParam(role, p.name, false)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, false)))
                    } else {
                        add(StorageDecl(translateType(p.type), Visibility.PUBLIC, storageParam(role, p.name, false)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, false)))
                    }
                    definedFields.add(field)
                }
            }
        }
    }
}

/**
 * Build DAG-specific modifiers.
 */
private fun buildDagModifiers(numActions: Int): List<ModifierDecl> = listOf(
    // modifier depends(uint actionId) { require(actionDone[actionId], "dependency not satisfied"); _; }
    ModifierDecl(
        name = "depends",
        params = listOf(Param(SolType.Uint256, "actionId")),
        body = listOf(
            require(
                index("actionDone", v("actionId")),
                "dependency not satisfied"
            )
        )
    ),
    // modifier notDone(uint actionId) { require(!actionDone[actionId], "already done"); _; }
    ModifierDecl(
        name = "notDone",
        params = listOf(Param(SolType.Uint256, "actionId")),
        body = listOf(
            require(
                not(index("actionDone", v("actionId"))),
                "already done"
            )
        )
    ),
    // modifier by(Role r) { require(role[msg.sender] == r, "bad role"); _; }
    ModifierDecl(
        name = "by",
        params = listOf(Param(SolType.EnumType(ROLE_ENUM), "r")),
        body = listOf(
            require(index(ROLE_MAPPING, msgSender) eq v("r"), "bad role")
        )
    ),
    // modifier at_final_phase() { require(all actions done && !payoffs_distributed); _; }
    ModifierDecl(
        name = "at_final_phase",
        params = emptyList(),
        body = listOf(
            // Check all actions done
            // For simplicity, check that highest-numbered action is done
            // TODO: Could be more robust
            require(index("actionDone", int(numActions - 1)), "game not over"),
            require(not(v("payoffs_distributed")), "payoffs already sent")
        )
    )
)

/**
 * Build per-action functions based on DAG.
 */
private fun buildActionFunctions(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    history: ParamHistory
): List<FunctionDecl> = buildList {
    // Generate functions in topological order
    dag.topo().forEach { actionId ->
        val (role, phaseIdx) = actionId
        val phase = g.phases[phaseIdx]
        val sig = phase.actions[role]!!
        val actionIdx = linearization[actionId]!!

        // Collect dependencies
        val deps = dag.prerequisitesOf(actionId)
        val depModifiers = deps.map { dep ->
            ModifierCall("depends", listOf(int(linearization[dep]!!)))
        }

        // Determine function type
        val isReveal = sig.parameters.any { p -> history.isReveal(role, p.name, phaseIdx) }
        val needsCR = history.needsCommitReveal(role, sig, phaseIdx)

        val function = when {
            isReveal -> buildDagReveal(role, sig, phaseIdx, actionIdx, depModifiers, g, history)
            needsCR -> buildDagCommit(role, sig, phaseIdx, actionIdx, depModifiers, g, history)
            sig.join != null -> {
                if (sig.parameters.isEmpty()) {
                    buildDagSimpleJoin(role, sig, phaseIdx, actionIdx, depModifiers, g, history)
                } else {
                    buildDagJoinVisible(role, sig, phaseIdx, actionIdx, depModifiers, g, history)
                }
            }
            else -> buildDagYield(role, sig, phaseIdx, actionIdx, depModifiers, g, history)
        }

        add(function)
    }
}

/**
 * DAG-based simple join (no parameters).
 */
private fun buildDagSimpleJoin(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    actionIdx: Int,
    depModifiers: List<ModifierCall>,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    return FunctionDecl(
        name = actionFuncName(role, phaseIdx),
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(NO_ROLE),
            ModifierCall("notDone", listOf(int(actionIdx)))
        ) + depModifiers,
        body = buildList {
            addAll(buildJoinLogic(role, sig))
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            add(assign(index("actionDone", int(actionIdx)), bool(true)))
            add(assign(index("actionTimestamp", int(actionIdx)), SolExpr.Member(SolExpr.Var("block"), "timestamp")))
        }
    )
}

/**
 * DAG-based join with visible parameters.
 */
private fun buildDagJoinVisible(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    actionIdx: Int,
    depModifiers: List<ModifierCall>,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = actionFuncName(role, phaseIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(NO_ROLE),
            ModifierCall("notDone", listOf(int(actionIdx)))
        ) + depModifiers,
        body = buildList {
            addAll(buildJoinLogic(role, sig))
            addAll(translateDomainGuards(sig.parameters))
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            addAll(translateAssignments(role, sig.parameters))
            add(assign(index("actionDone", int(actionIdx)), bool(true)))
            add(assign(index("actionTimestamp", int(actionIdx)), SolExpr.Member(SolExpr.Var("block"), "timestamp")))
        }
    )
}

/**
 * DAG-based yield.
 */
private fun buildDagYield(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    actionIdx: Int,
    depModifiers: List<ModifierCall>,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = actionFuncName(role, phaseIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(role),
            ModifierCall("notDone", listOf(int(actionIdx)))
        ) + depModifiers,
        body = buildList {
            addAll(translateDomainGuards(sig.parameters))
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            addAll(translateAssignments(role, sig.parameters))
            add(assign(index("actionDone", int(actionIdx)), bool(true)))
            add(assign(index("actionTimestamp", int(actionIdx)), SolExpr.Member(SolExpr.Var("block"), "timestamp")))
        }
    )
}

/**
 * DAG-based commit.
 */
private fun buildDagCommit(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    actionIdx: Int,
    depModifiers: List<ModifierCall>,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val hiddenParams = sig.parameters.filter { !it.visible }
    val inputs = hiddenParams.map { p ->
        Param(SolType.Uint256, inputParam(p.name, hidden = true))
    }

    val body = buildList {
        addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
        hiddenParams.forEach { p ->
            val pName = p.name
            add(
                assign(
                    v(storageParam(role, pName, hidden = true)),
                    v(inputParam(pName, hidden = true))
                )
            )
            add(
                assign(
                    v(doneFlag(role, pName, hidden = true)),
                    bool(true)
                )
            )
        }
        add(assign(index("actionDone", int(actionIdx)), bool(true)))
        add(assign(index("actionTimestamp", int(actionIdx)), SolExpr.Member(SolExpr.Var("block"), "timestamp")))
    }.toMutableList()

    val deposit = sig.join?.deposit?.v ?: 0
    val byRole = if (sig.join != null) NO_ROLE else role
    if (sig.join != null) {
        body.addAll(0, buildJoinLogic(role, sig))
    }

    return FunctionDecl(
        name = actionFuncName(role, phaseIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(byRole),
            ModifierCall("notDone", listOf(int(actionIdx)))
        ) + depModifiers,
        body = body
    )
}

/**
 * DAG-based reveal.
 */
private fun buildDagReveal(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    actionIdx: Int,
    depModifiers: List<ModifierCall>,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val clearParams = sig.parameters.filter { it.visible }
    val inputs = buildList {
        clearParams.forEach { p ->
            add(Param(translateType(p.type), inputParam(p.name, hidden = false)))
        }
        add(Param(SolType.Uint256, "salt"))
    }

    val body = buildList {
        // Verify commitments
        clearParams.forEach { p ->
            if (history.isReveal(role, p.name, phaseIdx)) {
                val computed = SolExpr.Keccak256(
                    SolExpr.AbiEncodePacked(
                        listOf(
                            v(inputParam(p.name, false)),
                            v("salt")
                        )
                    )
                )
                val stored = v(storageParam(role, p.name, hidden = true))
                add(require(computed eq SolExpr.Cast(SolType.Bytes32, stored), "bad reveal"))
            }
        }

        addAll(translateDomainGuards(clearParams))
        addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
        addAll(translateAssignments(role, clearParams))
        add(assign(index("actionDone", int(actionIdx)), bool(true)))
        add(assign(index("actionTimestamp", int(actionIdx)), SolExpr.Member(SolExpr.Var("block"), "timestamp")))
    }

    return FunctionDecl(
        name = actionFuncName(role, phaseIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(role),
            ModifierCall("notDone", listOf(int(actionIdx)))
        ) + depModifiers,
        body = body
    )
}

/**
 * DAG-based payoff function.
 */
private fun buildDagPayoffFunction(g: GameIR, history: ParamHistory, finalPhase: Int): FunctionDecl {
    val body = buildList<Statement> {
        add(assign(v("payoffs_distributed"), bool(true)))

        (g.roles + g.chanceRoles).forEach { role ->
            val payoffExpr = g.payoffs[role] ?: return@forEach

            // Use finalPhase for context, even though we're DAG-based
            val solPayoff = translateIrExpr(
                payoffExpr,
                g,
                history,
                role,
                finalPhase,
                ExprContext.PAYOFF
            )

            val roleAddr = v(roleAddr(role))
            add(assign(index(BALANCE_MAPPING, roleAddr), solPayoff))
        }
    }

    return FunctionDecl(
        name = "distributePayoffs",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(ModifierCall("at_final_phase", emptyList())),
        body = body
    )
}

// Helper to create modifier call
private fun by(roleId: RoleId): ModifierCall = ModifierCall("by", listOf(role(roleId.name)))
private fun role(byRole: String): SolExpr.EnumValue = enumVal(ROLE_ENUM, byRole)

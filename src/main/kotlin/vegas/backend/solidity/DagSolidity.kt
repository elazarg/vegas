package vegas.backend.solidity

import vegas.RoleId
import vegas.FieldRef
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.ActionGameIR
import vegas.ir.ActionMeta
import vegas.ir.ActionParam
import vegas.ir.ActionKind
import vegas.ir.ActionSpec
import vegas.ir.Expr
import vegas.ir.Type


val NO_ROLE = RoleId("None")

/**
 * Defines the context in which an IR expression is being translated.
 * - WHERE_CLAUSE: Reading from function inputs and current storage.
 * - PAYOFF: Reading from final, post-game storage.
 */
enum class ExprContext { WHERE_CLAUSE, PAYOFF }

/**
 * DAG-based Solidity backend.
 * Generates contracts using action dependencies instead of phase barriers.
 */

/**
 * Linearize ActionDag to assign sequential integer IDs to actions.
 *
 * We use a deterministic order: topo order, tie-broken by (phase index, role name).
 * The second component of ActionId is currently the legacy phase index.
 */
fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.topo()
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()

/**
 * Generate action constant name (e.g., "ACTION_Alice_0").
 *
 * The integer here is the linearization index, not the original phase index.
 */
fun actionConstName(role: RoleId, index: Int): String =
    "ACTION_${role.name}_$index"

/**
 * Generate action function name (e.g., "move_Alice_0").
 *
 * The integer here is the linearization index, not the original phase index.
 */
fun actionFuncName(role: RoleId, index: Int): String =
    "move_${role.name}_$index"

/**
 * Main entry: Generate Solidity from ActionGameIR / ActionDag.
 *
 * Upstream is responsible for:
 *  - expanding commit–reveal in the IR, and
 *  - constructing the ActionDag from that normalized IR.
 */
fun genSolidity(game: ActionGameIR): String {
    val solAst = irToDagSolidity(game)
    return renderSolidityContract(solAst)
}


/** Withdraw function (matches golden) */
private fun buildWithdraw(): FunctionDecl {
    val bal = "bal"
    return FunctionDecl(
        name = "withdraw",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = emptyList(),
        body = listOf(
            // int256 bal = balanceOf[msg.sender];
            Statement.VarDecl(SolType.Int256, bal, index(BALANCE_MAPPING, msgSender)),
            // require(bal > 0, "no funds");
            require(v(bal) gt int(0), "no funds"),
            // Effects-first: balanceOf[msg.sender] = 0;
            assign(index(BALANCE_MAPPING, msgSender), int(0)),
            // Interaction: (bool ok, ) = payable(msg.sender).call{value: bal}("");
            Statement.Raw("(bool ok, ) = payable(msg.sender).call{value: uint256($bal)}(\"\");"),
            require(v("ok"), "ETH send failed")
        )
    )
}

/**
 * Translate ActionGameIR (roles + ActionDag + payoffs) to SolidityContract AST.
 */
fun irToDagSolidity(g: ActionGameIR): SolidityContract {
    // Temporary name: g.phases currently holds the ActionDag.
    val dag = g.phases
    val linearization = linearizeDag(dag)

    // Constructor: set lastTs = block.timestamp
    val ctor = Constructor(
        body = listOf(
            assign(v(LAST_TS_VAR), blockTimestamp)
        )
    )

    // Role enum (None + all roles)
    val roleEnum = EnumDecl(
        name = ROLE_ENUM,
        values = (listOf(NO_ROLE) + g.roles + g.chanceRoles).map { it.name }
    )

    // Storage (no phase variable, add actionDone/actionTimestamp etc.)
    val storage = buildDagGameStorage(g, dag, linearization)

    // Modifiers (depends, notDone, by, at_final_phase)
    val modifiers = buildDagModifiers(dag, linearization)

    // Functions (per-action + payoff + withdraw)
    val functions = buildList {
        // Per-action functions generated directly from the DAG
        addAll(buildActionFunctions(dag, linearization))

        // Payoff distribution at the terminal configuration
        add(buildDagPayoffFunction(g))

        // Withdraw
        add(buildWithdraw())
    }

    // Events (could generate per-action events if desired)
    val events = emptyList<EventDecl>()

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
    g: ActionGameIR,
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

    // Action constants (indexed by linearization index, not legacy phase index)
    linearization.forEach { (actionId, idx) ->
        val role = dag.owner(actionId)
        add(
            StorageDecl(
                type = SolType.Uint256,
                visibility = Visibility.PUBLIC,
                name = actionConstName(role, idx),
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

    /* ---------------------------------------------------------------------- */
    /*  Game state storage (per-field), derived from ActionDag                */
    /* ---------------------------------------------------------------------- */

    // 1) Which roles ever have a join step? → per-role "joined" flag.
    val rolesWithJoin = mutableSetOf<RoleId>()
    dag.metas.forEach { meta ->
        if (meta.spec.join != null) {
            rolesWithJoin += meta.struct.role
        }
    }
    rolesWithJoin.forEach { role ->
        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, roleDone(role)))
    }

    // 2) Compute field → type, based on action parameters.
    val fieldTypes = mutableMapOf<FieldRef, Type>()
    dag.metas.forEach { meta ->
        val role = meta.struct.role
        meta.spec.params.forEach { p ->
            val field = FieldRef(role, p.name)
            fieldTypes.putIfAbsent(field, p.type)
        }
    }

    // 3) Which fields participate in commit/reveal?
    // If any action has Visibility.COMMIT or Visibility.REVEAL on a field,
    // we need hidden+clear storage and both done flags for that field.
    val fieldsNeedingCommitReveal = mutableSetOf<FieldRef>()
    dag.metas.forEach { meta ->
        meta.struct.visibility.forEach { (field, vis) ->
            if (vis == vegas.ir.Visibility.COMMIT || vis == vegas.ir.Visibility.REVEAL) {
                fieldsNeedingCommitReveal += field
            }
        }
    }

    // 4) Allocate storage per logical field, once.
    val definedFields = mutableSetOf<FieldRef>()
    dag.metas.forEach { meta ->
        val role = meta.struct.role
        meta.struct.writes.forEach { field ->
            if (!definedFields.add(field)) return@forEach

            val ty = fieldTypes[field]
                ?: error("Missing type information for field $field")

            if (field in fieldsNeedingCommitReveal) {
                // Hidden (hash) cell + done flag
                add(
                    StorageDecl(
                        SolType.Uint256,
                        Visibility.PUBLIC,
                        storageParam(role, field.param, true)
                    )
                )
                add(
                    StorageDecl(
                        SolType.Bool,
                        Visibility.PUBLIC,
                        doneFlag(role, field.param, true)
                    )
                )

                // Clear cell + done flag
                add(
                    StorageDecl(
                        translateType(ty),
                        Visibility.PUBLIC,
                        storageParam(role, field.param, false)
                    )
                )
                add(
                    StorageDecl(
                        SolType.Bool,
                        Visibility.PUBLIC,
                        doneFlag(role, field.param, false)
                    )
                )
            } else {
                // Purely public field: clear cell + done flag only
                add(
                    StorageDecl(
                        translateType(ty),
                        Visibility.PUBLIC,
                        storageParam(role, field.param, false)
                    )
                )
                add(
                    StorageDecl(
                        SolType.Bool,
                        Visibility.PUBLIC,
                        doneFlag(role, field.param, false)
                    )
                )
            }
        }
    }
}

/**
 * Build DAG-based modifiers.
 *
 * - depends(a):    require that action a is already done
 * - notDone(a):    require that action a is not yet done
 * - by(r):         require that msg.sender has role r (or NO_ROLE for open joins)
 * - at_final_phase:
 *      require that the "terminal" action is done and that payoffs have not yet
 *      been distributed.
 *
 * "Terminal" is defined as:
 *   - the max linearization index among REVEAL actions, if any exist; otherwise
 *   - the max linearization index among all actions.
 */
private fun buildDagModifiers(
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): List<ModifierDecl> {
    // 1. Find candidate terminal actions
    val revealIds = dag.metas
        .filter { it.kind == ActionKind.REVEAL }
        .map { it.id }

    val finalActionIdx: Int = if (revealIds.isNotEmpty()) {
        revealIds.maxOf { id -> linearization.getValue(id) }
    } else {
        // No reveals at all: fall back to the last action in the linearization
        linearization.values.max()
    }

    return listOf(
        // modifier depends(uint actionId) {
        //   require(actionDone[actionId], "dependency not satisfied");
        //   _;
        // }
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

        // modifier notDone(uint actionId) {
        //   require(!actionDone[actionId], "already done");
        //   _;
        // }
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

        // modifier by(Role r) {
        //   require(role[msg.sender] == r, "bad role");
        //   _;
        // }
        ModifierDecl(
            name = "by",
            params = listOf(Param(SolType.EnumType(ROLE_ENUM), "r")),
            body = listOf(
                require(
                    index(ROLE_MAPPING, msgSender) eq v("r"),
                    "bad role"
                )
            )
        ),

        // modifier at_final_phase() {
        //   require(actionDone[FINAL_ACTION_IDX], "game not over");
        //   require(!payoffs_distributed, "payoffs already sent");
        //   _;
        // }
        ModifierDecl(
            name = "at_final_phase",
            params = emptyList(),
            body = listOf(
                require(
                    index("actionDone", int(finalActionIdx)),
                    "game not over"
                ),
                require(
                    not(v("payoffs_distributed")),
                    "payoffs already sent"
                )
            )
        )
    )
}

/**
 * Build per-action functions based on the ActionDag.
 */
private fun buildActionFunctions(
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): List<FunctionDecl> = buildList {
    // Generate functions in topological order for determinism
    dag.topo().forEach { actionId ->
        val meta = dag.meta(actionId)
        val actionIdx = linearization.getValue(actionId)

        // Collect dependency modifiers from prerequisites
        val depModifiers = dag.prerequisitesOf(actionId).map { dep ->
            depends(linearization.getValue(dep))
        }

        val fn = when (meta.kind) {
            ActionKind.YIELD  -> buildDagYield(meta, actionIdx, depModifiers)
            ActionKind.COMMIT -> buildDagCommit(meta, actionIdx, depModifiers)
            ActionKind.REVEAL -> buildDagReveal(meta, actionIdx, depModifiers)
            ActionKind.JOIN   -> error("ActionKind.JOIN should not be used; join is handled in YIELD")
        }

        add(fn)
    }
}

/**
 * Helper function to generate the common "join" logic.
 * This includes role assignment, address saving, deposit handling, and 'done' flag.
 */
private fun buildJoinLogic(role: RoleId, spec: ActionSpec): List<Statement> {
    val deposit = spec.join?.deposit?.v ?: 0
    val statements = mutableListOf<Statement>()

    // Ensure the role hasn't joined yet
    statements.add(require(not(v(roleDone(role))), "already joined"))

    // Assign role to msg.sender
    statements.add(assign(index(ROLE_MAPPING, msgSender), role(role.name)))
    statements.add(assign(v(roleAddr(role)), msgSender)) // Save address

    // Deposit handling (if any)
    if (deposit > 0) {
        statements.add(requireDeposit(deposit))
        statements.add(setBalance())
    }

    // Mark as joined
    statements.add(assign(v(roleDone(role)), bool(true)))

    return statements
}
/** DAG-based yield (plain visible write, may include join). */
private fun buildDagYield(
    meta: ActionMeta,
    actionIdx: Int,
    depModifiers: List<ModifierCall>
): FunctionDecl {
    val role = meta.struct.role
    val spec = meta.spec

    val isJoin = spec.join != null
    val deposit = spec.join?.deposit?.v ?: 0

    val inputs = spec.params.map { p ->
        Param(translateType(p.type), inputParam(p.name, hidden = false))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE
        else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(if (isJoin) NO_ROLE else role),
            notDone(actionIdx)
        ) + depModifiers,
        body = buildList {
            if (isJoin) {
                addAll(buildJoinLogic(role, spec))
            }
            addAll(translateDomainGuards(spec.params))
            addAll(translateWhere(spec.guardExpr, role, spec.params))
            addAll(translateAssignments(role, spec.params))
            add(assign(index("actionDone", int(actionIdx)), bool(true)))
            add(assign(index("actionTimestamp", int(actionIdx)), blockTimestamp))
        }
    )
}

/** DAG-based commit. */
private fun buildDagCommit(
    meta: ActionMeta,
    actionIdx: Int,
    depModifiers: List<ModifierCall>
): FunctionDecl {
    val role   = meta.struct.role
    val spec   = meta.spec
    val struct = meta.struct

    val isJoin  = spec.join != null
    val deposit = spec.join?.deposit?.v ?: 0

    val commitParams = spec.params.filter { p ->
        FieldRef(role, p.name) in struct.commitFields
    }

    val inputs = commitParams.map { p ->
        Param(SolType.Uint256, inputParam(p.name, hidden = true))
    }

    val byRole =
        if (isJoin) NO_ROLE else role

    val body = buildList {
        // For join commits, do the join logic here (role assignment, deposit, done_role flag)
        if (isJoin) {
            addAll(buildJoinLogic(role, spec))
        }

        // Guard: usually 'true' for commit nodes after expandCommitReveal, but harmless
        addAll(translateWhere(spec.guardExpr, role, spec.params))

        // Store hidden commits for each committed field
        commitParams.forEach { p ->
            val pName = p.name
            add(assign(
                v(storageParam(role, pName, hidden = true)),
                v(inputParam(pName, hidden = true))
            ))
            add(assign(
                v(doneFlag(role, pName, hidden = true)),
                bool(true)
            ))
        }

        add(assign(index("actionDone", int(actionIdx)), bool(true)))
        add(assign(index("actionTimestamp", int(actionIdx)), blockTimestamp))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0)
            StateMutability.PAYABLE
        else
            StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(byRole),
            notDone(actionIdx)
        ) + depModifiers,
        body = body
    )
}


/** DAG-based reveal. */
private fun buildDagReveal(
    meta: ActionMeta,
    actionIdx: Int,
    depModifiers: List<ModifierCall>
): FunctionDecl {
    val role   = meta.struct.role
    val spec   = meta.spec
    val struct = meta.struct

    val revealParams = spec.params.filter { p ->
        FieldRef(role, p.name) in struct.revealFields
    }

    val inputs = buildList {
        revealParams.forEach { p ->
            add(Param(translateType(p.type), inputParam(p.name, hidden = false)))
        }
        add(Param(SolType.Uint256, "salt"))
    }

    val body = buildList {
        revealParams.forEach { p ->
            val computed = SolExpr.Keccak256(
                SolExpr.AbiEncodePacked(
                    listOf(
                        v(inputParam(p.name, hidden = false)),
                        v("salt")
                    )
                )
            )
            val stored = v(storageParam(role, p.name, hidden = true))
            add(
                require(
                    computed eq toBytes32(stored),
                    "bad reveal"
                )
            )
        }

        addAll(translateDomainGuards(revealParams))
        addAll(translateWhere(spec.guardExpr, role, spec.params))
        addAll(translateAssignments(role, revealParams))

        add(assign(index("actionDone", int(actionIdx)), bool(true)))
        add(assign(index("actionTimestamp", int(actionIdx)), blockTimestamp))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(role),
            notDone(actionIdx)
        ) + depModifiers,
        body = body
    )
}


/**
 * DAG-based payoff function.
 *
 * Payoffs are evaluated once, at the terminal configuration
 * (enforced by the at_final_phase modifier).
 */
private fun buildDagPayoffFunction(
    g: ActionGameIR
): FunctionDecl {
    val body = buildList<Statement> {
        add(assign(v("payoffs_distributed"), bool(true)))

        (g.roles + g.chanceRoles).forEach { role ->
            val payoffExpr = g.payoffs[role] ?: return@forEach

            val solPayoff = translateIrExprAtTerminal(payoffExpr, role)
            val roleAddrExpr = v(roleAddr(role))

            add(assign(index(BALANCE_MAPPING, roleAddrExpr), solPayoff))
        }
    }

    return FunctionDecl(
        name = "distributePayoffs",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(atFinalPhase()),
        body = body
    )
}



/* ====================== IR->Solidity translation atoms ====================== */

internal fun translateType(t: Type): SolType = when (t) {
    is Type.IntType -> SolType.Int256
    is Type.BoolType -> SolType.Bool
    is Type.SetType -> SolType.Int256 // Enums/sets are represented as integers
}

/**
 * Translates a vegas.ir.Expr into a vegas.backend.solidity.SolExpr.
 *
 * This is the core logic engine used for both:
 *  - WHERE_CLAUSE: guards of individual actions
 *  - PAYOFF:       terminal payoff expressions
 *
 * The crucial design decision:
 *  - Guards see *current action inputs* for fields that are parameters
 *    of the current action (same role, same name).
 *  - All other field reads (including in payoffs) use the clear
 *    on-chain storage cell, not the hidden commit hash.
 */
internal fun translateIrExpr(
    expr: Expr,
    currentRole: RoleId,
    currentParams: List<ActionParam>,
    context: ExprContext
): SolExpr = when (expr) {
    // Literals
    is Expr.IntVal  -> int(expr.v)
    is Expr.BoolVal -> bool(expr.v)

    // Field access
    is Expr.Field -> {
        val (role, param) = expr.field

        // Is this field an input to the *current* action?
        val isInput =
            context == ExprContext.WHERE_CLAUSE &&
                    role == currentRole &&
                    currentParams.any { it.name == param }

        if (isInput) {
            // Read from function input (e.g., "_param_x").
            // Commit–reveal is handled structurally by COMMIT/REVEAL actions,
            // so guards only see clear values.
            v(inputParam(param, hidden = false))
        } else {
            // Read from storage (e.g., "Alice_x_visible").
            // For both WHERE_CLAUSE and PAYOFF contexts, we read the clear value.
            v(storageParam(role, param, hidden = false))
        }
    }

    // isDefined(field) → use the clear done-flag
    is Expr.IsDefined -> {
        val (role, param) = expr.field
        v(doneFlag(role, param, hidden = false))
    }

    // --- Arithmetic ---
    is Expr.Add ->
        translateIrExpr(expr.l, currentRole, currentParams, context) +
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Sub ->
        translateIrExpr(expr.l, currentRole, currentParams, context) -
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Mul ->
        translateIrExpr(expr.l, currentRole, currentParams, context) *
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Div ->
        translateIrExpr(expr.l, currentRole, currentParams, context) /
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Neg ->
        neg(translateIrExpr(expr.x, currentRole, currentParams, context))

    // --- Comparison ---
    is Expr.Eq ->
        translateIrExpr(expr.l, currentRole, currentParams, context) eq
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Ne ->
        translateIrExpr(expr.l, currentRole, currentParams, context) ne
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Lt ->
        translateIrExpr(expr.l, currentRole, currentParams, context) lt
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Le ->
        translateIrExpr(expr.l, currentRole, currentParams, context) le
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Gt ->
        translateIrExpr(expr.l, currentRole, currentParams, context) gt
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Ge ->
        translateIrExpr(expr.l, currentRole, currentParams, context) ge
                translateIrExpr(expr.r, currentRole, currentParams, context)

    // --- Boolean ---
    is Expr.And ->
        translateIrExpr(expr.l, currentRole, currentParams, context) and
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Or ->
        translateIrExpr(expr.l, currentRole, currentParams, context) or
                translateIrExpr(expr.r, currentRole, currentParams, context)

    is Expr.Not ->
        not(translateIrExpr(expr.x, currentRole, currentParams, context))

    // --- Ternary ---
    is Expr.Ite -> SolExpr.Ternary(
        condition = translateIrExpr(expr.c, currentRole, currentParams, context),
        ifTrue   = translateIrExpr(expr.t, currentRole, currentParams, context),
        ifFalse  = translateIrExpr(expr.e, currentRole, currentParams, context)
    )
}

/** Generates 'require' statements for domain validation (e.g., `x in {1, 2, 3}`) */
internal fun translateDomainGuards(params: List<ActionParam>): List<Statement.Require> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = v(inputParam(p.name, false))
                    val cond = t.values.map { x eq int(it) }.reduce<SolExpr, SolExpr> { a, b -> a or b }
                    require(cond, "domain")
                }
            }

            else -> null
        }
    }

/** Generates assignment statements to store visible parameters and set their done flags. */
private fun translateAssignments(role: RoleId, params: List<ActionParam>): List<Statement.Assign> =
    params.flatMap { p ->
        val storage = v(storageParam(role, p.name, false))
        val input = v(inputParam(p.name, false))
        val done = v(doneFlag(role, p.name, false))
        listOf(assign(storage, input), assign(done, bool(true)))
    }


/** Translates the IR 'where' condition into Solidity 'require' statements. */
private fun translateWhere(
    expr: Expr,
    role: RoleId,
    currentParams: List<ActionParam>
): List<Statement.Require> {
    // Don't emit a trivial `require(true)`
    if (expr == Expr.BoolVal(true)) return emptyList()

    val solCondition = translateIrExpr(
        expr          = expr,
        currentRole   = role,
        currentParams = currentParams,
        context       = ExprContext.WHERE_CLAUSE
    )
    return listOf(require(solCondition, "where"))
}

/**
 * Translate a payoff expression at the terminal configuration.
 *
 * Payoffs are evaluated after all actions are done; they only read the
 * final clear storage cells.
 */
private fun translateIrExprAtTerminal(
    expr: Expr,
    role: RoleId
): SolExpr =
    translateIrExpr(
        expr          = expr,
        currentRole   = role,
        currentParams = emptyList(),
        context       = ExprContext.PAYOFF
    )


// Helper to create modifier call
private fun by(roleId: RoleId): ModifierCall = ModifierCall("by", listOf(role(roleId.name)))
private fun role(byRole: String): SolExpr.EnumValue = enumVal(ROLE_ENUM, byRole)

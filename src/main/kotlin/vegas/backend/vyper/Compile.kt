package vegas.backend.vyper

import vegas.RoleId
import vegas.FieldRef
import vegas.backend.vyper.VyExpr.*
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.GameIR
import vegas.ir.ActionMeta
import vegas.ir.ActionParam
import vegas.ir.ActionSpec
import vegas.ir.Expr
import vegas.ir.Type

/**
 * SEMANTIC: Expression context is identical to Solidity.
 * - WHERE_CLAUSE: Reading from function inputs and current storage.
 * - PAYOFF: Reading from final, post-game storage.
 */
enum class ExprContext { WHERE_CLAUSE, PAYOFF }

/**
 * DAG-based Vyper backend.
 */

/**
 * SEMANTIC: DAG linearization is identical to Solidity.
 * Assigns sequential integer IDs to actions in topological order.
 */
fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.topo()
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()

/**
 * Main entry: Generate Vyper from GameIR / ActionDag.
 *
 * Upstream is responsible for:
 *  - expanding commit–reveal in the IR, and
 *  - constructing the ActionDag from that normalized IR.
 */
fun genVyper(game: GameIR): String {
    val vyAst = irToVyper(game)
    return renderVyperModule(vyAst)
}

/**
 * Translate GameIR (roles + ActionDag + payoffs) to VyperModule AST.
 */
fun irToVyper(g: GameIR): VyperModule {
    val dag = g.dag
    val linearization = linearizeDag(dag)

    // Constructor: set lastTs = block.timestamp
    val constructor = Constructor(
        body = listOf(
            assign(selfMember(LAST_TS_VAR), blockTimestamp)
        )
    )

    // Role enum (None + all roles)
    val roleEnum = EnumDecl(
        name = ROLE_ENUM,
        values = (listOf(NO_ROLE) + g.roles + g.chanceRoles).map { it.name }
    )

    // Constants (action IDs + FINAL_ACTION)
    val constants = buildActionConstants(dag, linearization)

    // Storage
    val storage = buildVyperStorage(g, dag)

    // Functions (per-action + payoff + withdraw + internal helpers + default)
    val functions = buildList {
        // Internal helper functions
        add(buildCheckRevealHelper())
        add(buildMarkActionDoneHelper())

        // Per-action functions generated directly from the DAG
        addAll(buildActionFunctions(dag, linearization))

        // Payoff distribution at the terminal configuration
        add(buildVyperPayoffFunction(g))

        // Withdraw
        add(buildWithdraw())

        // Default (fallback) function
        add(buildDefaultFunction())
    }

    return VyperModule(
        version = VYPER_VERSION,
        enums = listOf(roleEnum),
        constants = constants,
        storage = storage,
        constructor = constructor,
        functions = functions
    )
}

/**
 * Build action constants.
 * SEMANTIC: Identical to Solidity - ACTION_Role_idx constants and FINAL_ACTION.
 */
private fun buildActionConstants(
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): List<ConstantDecl> = buildList {
    linearization.forEach { (actionId, idx) ->
        val owner = dag.owner(actionId)
        add(ConstantDecl(
            type = VyType.Uint256,
            name = actionConstName(owner, idx),
            value = int(idx)
        ))
    }

    // FINAL_ACTION constant (terminal action for payoff distribution)
    val revealIds = dag.metas
        .filter { it.kind == vegas.ir.Visibility.REVEAL }
        .map { it.id }
    val finalActionIdx: Int = if (revealIds.isNotEmpty()) {
        revealIds.maxOf { id -> linearization.getValue(id) }
    } else {
        linearization.values.maxOrNull() ?: 0
    }
    add(ConstantDecl(
        type = VyType.Uint256,
        name = "FINAL_ACTION",
        value = int(finalActionIdx)
    ))
}

/**
 * Build storage for Vyper contract.
 * SEMANTIC: Storage model is identical to Solidity - role tracking, balances, game state.
 */
private fun buildVyperStorage(
    g: GameIR,
    dag: ActionDag,
): List<StorageDecl> = buildList {
    // Timing
    add(StorageDecl(VyType.Uint256, LAST_TS_VAR))

    // Action tracking
    add(StorageDecl(
        type = VyType.HashMap(VyType.Uint256, VyType.Bool),
        name = "actionDone"
    ))
    add(StorageDecl(
        type = VyType.HashMap(VyType.Uint256, VyType.Uint256),
        name = "actionTimestamp"
    ))

    // Roles and balances
    add(StorageDecl(
        type = VyType.HashMap(VyType.Address, VyType.EnumType(ROLE_ENUM)),
        name = ROLE_MAPPING
    ))
    add(StorageDecl(
        type = VyType.HashMap(VyType.Address, VyType.Int256),
        name = BALANCE_MAPPING
    ))

    // Player addresses
    g.roles.forEach { role ->
        add(StorageDecl(VyType.Address, roleAddr(role)))
    }
    g.chanceRoles.forEach { role ->
        add(StorageDecl(VyType.Address, roleAddr(role)))
    }

    // Payoff distribution flag
    add(StorageDecl(VyType.Bool, "payoffs_distributed"))

    /* ---------------------------------------------------------------------- */
    /*  Game state storage (per-field), derived from ActionDag                */
    /* ---------------------------------------------------------------------- */

    // 1) Which roles ever have a join step? -> per-role "joined" flag.
    val rolesWithJoin = mutableSetOf<RoleId>()
    dag.metas.forEach { meta ->
        if (meta.spec.join != null) {
            rolesWithJoin += meta.struct.owner
        }
    }
    rolesWithJoin.forEach { role ->
        add(StorageDecl(VyType.Bool, roleDone(role)))
    }

    // 2) Compute field -> type, based on action parameters.
    val fieldTypes = mutableMapOf<FieldRef, Type>()
    dag.metas.forEach { meta ->
        val owner = meta.struct.owner
        meta.spec.params.forEach { p ->
            val field = FieldRef(owner, p.name)
            fieldTypes.putIfAbsent(field, p.type)
        }
    }

    // 3) Which fields participate in commit/reveal?
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
        val owner = meta.struct.owner
        meta.struct.writes.forEach { field ->
            if (!definedFields.add(field)) return@forEach

            val ty = fieldTypes[field]
                ?: error("Missing type information for field $field")

            if (field in fieldsNeedingCommitReveal) {
                // Hidden (hash) cell + done flag (stored as bytes32 hash)
                add(StorageDecl(
                    VyType.Bytes32,
                    storageParam(owner, field.param, true)
                ))
                add(StorageDecl(
                    VyType.Bool,
                    doneFlag(owner, field.param, true)
                ))

                // Clear cell + done flag
                add(StorageDecl(
                    translateType(ty),
                    storageParam(owner, field.param, false)
                ))
                add(StorageDecl(
                    VyType.Bool,
                    doneFlag(owner, field.param, false)
                ))
            } else {
                // Purely public field: clear cell + done flag only
                add(StorageDecl(
                    translateType(ty),
                    storageParam(owner, field.param, false)
                ))
                add(StorageDecl(
                    VyType.Bool,
                    doneFlag(owner, field.param, false)
                ))
            }
        }
    }
}

/**
 * Build internal helper: _checkReveal
 * SEMANTIC: Identical commit-reveal verification (keccak256).
 */
private fun buildCheckRevealHelper(): FunctionDecl {
    return FunctionDecl(
        name = "_checkReveal",
        params = listOf(
            Param(VyType.Bytes32, "commitment"),
            Param(VyType.DynBytes(ABI_ENCODE_BYTES_SIZE), "preimage")
        ),
        decorators = listOf(
            Decorator.Internal,
            Decorator.View
        ),
        body = listOf(
            vyAssert(
                vyKeccak256(v("preimage")) eq v("commitment"),
                "bad reveal"
            )
        )
    )
}

/**
 * Build internal helper: _markActionDone
 * SEMANTIC: Identical action tracking logic.
 */
private fun buildMarkActionDoneHelper(): FunctionDecl {
    return FunctionDecl(
        name = "_markActionDone",
        params = listOf(Param(VyType.Uint256, "actionId")),
        decorators = listOf(Decorator.Internal),
        body = listOf(
            assign(selfIndex("actionDone", v("actionId")), vyTrue),
            assign(selfIndex("actionTimestamp", v("actionId")), blockTimestamp),
            assign(selfMember(LAST_TS_VAR), blockTimestamp)
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

        val fn = when (meta.kind) {
            vegas.ir.Visibility.PUBLIC  -> buildVyperYield(meta, actionIdx, dag, linearization)
            vegas.ir.Visibility.COMMIT -> buildVyperCommit(meta, actionIdx, dag, linearization)
            vegas.ir.Visibility.REVEAL -> buildVyperReveal(meta, actionIdx, dag, linearization)
        }

        add(fn)
    }
}

/**
 * Helper function to generate the common "join" logic.
 * SEMANTIC: Identical to Solidity - role assignment, deposit handling.
 */
private fun buildJoinLogic(role: RoleId, spec: ActionSpec): List<Statement> {
    val deposit = spec.join?.deposit?.v ?: 0
    val statements = mutableListOf<Statement>()

    // Ensure the caller doesn't already have a role
    statements.add(vyAssert(
        selfIndex(ROLE_MAPPING, msgSender) eq enumVal(ROLE_ENUM, NO_ROLE.name),
        "already has a role"
    ))

    // Ensure the role hasn't joined yet
    statements.add(vyAssert(not(selfMember(roleDone(role))), "already joined"))

    // Assign role to msg.sender
    statements.add(assign(selfIndex(ROLE_MAPPING, msgSender), enumVal(ROLE_ENUM, role.name)))
    statements.add(assign(selfMember(roleAddr(role)), msgSender))

    // Deposit handling (if any)
    if (deposit > 0) {
        statements.add(vyAssert(msgValue eq int(deposit), "bad stake"))
        statements.add(assign(selfIndex(BALANCE_MAPPING, msgSender), msgValue))
    }

    // Mark as joined
    statements.add(assign(selfMember(roleDone(role)), vyTrue))

    return statements
}

/** Vyper yield (plain visible write, may include join).
 * KEY DIFFERENCE: Vyper uses inline asserts instead of modifiers.
 */
private fun buildVyperYield(
    meta: ActionMeta,
    actionIdx: Int,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): FunctionDecl {
    val role = meta.struct.owner
    val spec = meta.spec

    val isJoin = spec.join != null
    val deposit = spec.join?.deposit?.v ?: 0

    val inputs = spec.params.map { p ->
        Param(translateType(p.type), inputParam(p.name, hidden = false))
    }

    val decorators = buildList {
        add(Decorator.External)
        if (deposit > 0) add(Decorator.Payable)
    }

    val body = buildList {
        // Inline "by" modifier check (role assertion)
        add(assertRole(if (isJoin) NO_ROLE else role))

        // Inline "notDone" modifier check
        add(assertNotDone(actionIdx))

        // Inline "depends" modifier checks (dependencies)
        dag.prerequisitesOf(meta.id).forEach { depId ->
            add(assertDone(linearization.getValue(depId)))
        }

        // Join logic
        if (isJoin) {
            addAll(buildJoinLogic(role, spec))
        }

        // Domain guards, where clause, assignments
        addAll(translateDomainGuards(spec.params))
        addAll(translateWhere(spec.guardExpr, role, spec.params))
        addAll(translateAssignments(role, spec.params))

        // Mark action done
        add(exprStmt(call("self._markActionDone", int(actionIdx))))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        decorators = decorators,
        body = body
    )
}

/** Vyper commit. */
private fun buildVyperCommit(
    meta: ActionMeta,
    actionIdx: Int,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): FunctionDecl {
    val role   = meta.struct.owner
    val spec   = meta.spec
    val struct = meta.struct

    val isJoin  = spec.join != null
    val deposit = spec.join?.deposit?.v ?: 0

    val commitParams = spec.params.filter { p ->
        FieldRef(role, p.name) in struct.commitFields
    }

    val inputs = commitParams.map { p ->
        Param(VyType.Bytes32, inputParam(p.name, hidden = true))
    }

    val decorators = buildList {
        add(Decorator.External)
        if (deposit > 0) add(Decorator.Payable)
    }

    val byRole = if (isJoin) NO_ROLE else role

    val body = buildList {
        // Inline assertions (replacing modifiers)
        add(assertRole(byRole))
        add(assertNotDone(actionIdx))

        // Dependencies
        dag.prerequisitesOf(meta.id).forEach { depId ->
            add(assertDone(linearization.getValue(depId)))
        }

        // Join logic
        if (isJoin) {
            addAll(buildJoinLogic(role, spec))
        }

        // Guard (usually true for commit nodes)
        addAll(translateWhere(spec.guardExpr, role, spec.params))

        // Store hidden commits
        commitParams.forEach { p ->
            val pName = p.name
            add(assign(
                selfMember(storageParam(role, pName, hidden = true)),
                v(inputParam(pName, hidden = true))
            ))
            add(assign(
                selfMember(doneFlag(role, pName, hidden = true)),
                vyTrue
            ))
        }

        add(exprStmt(call("self._markActionDone", int(actionIdx))))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        decorators = decorators,
        body = body
    )
}

/** Vyper reveal. */
private fun buildVyperReveal(
    meta: ActionMeta,
    actionIdx: Int,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): FunctionDecl {
    val role   = meta.struct.owner
    val spec   = meta.spec
    val struct = meta.struct

    val revealParams = spec.params.filter { p ->
        FieldRef(role, p.name) in struct.revealFields
    }

    val inputs = buildList {
        revealParams.forEach { p ->
            add(Param(translateType(p.type), inputParam(p.name, hidden = false)))
        }
        add(Param(VyType.Uint256, "salt"))
    }

    val body = buildList {
        // Inline assertions
        add(assertRole(role))
        add(assertNotDone(actionIdx))

        // Dependencies
        dag.prerequisitesOf(meta.id).forEach { depId ->
            add(assertDone(linearization.getValue(depId)))
        }

        // Verify reveals
        revealParams.forEach { p ->
            val preimage = abiEncode(
                v(inputParam(p.name, hidden = false)),
                v("salt"),
                outputType = VyType.DynBytes(ABI_ENCODE_BYTES_SIZE)
            )
            val commitment = selfMember(storageParam(role, p.name, hidden = true))
            add(exprStmt(call("self._checkReveal", commitment, preimage)))
        }

        // Domain guards, where clause, assignments
        addAll(translateDomainGuards(revealParams))
        addAll(translateWhere(spec.guardExpr, role, spec.params))
        addAll(translateAssignments(role, revealParams))

        add(exprStmt(call("self._markActionDone", int(actionIdx))))
    }

    return FunctionDecl(
        name = actionFuncName(role, actionIdx),
        params = inputs,
        decorators = listOf(Decorator.External),
        body = body
    )
}

/**
 * Inline role assertion (replaces "by" modifier).
 */
private fun assertRole(role: RoleId): Statement.Assert {
    return vyAssert(
        selfIndex(ROLE_MAPPING, msgSender) eq enumVal(ROLE_ENUM, role.name),
        "bad role"
    )
}

/**
 * Inline notDone assertion.
 */
private fun assertNotDone(actionIdx: Int): Statement.Assert {
    return vyAssert(
        not(selfIndex("actionDone", int(actionIdx))),
        "already done"
    )
}

/**
 * Inline depends assertion.
 */
private fun assertDone(actionIdx: Int): Statement.Assert {
    return vyAssert(
        selfIndex("actionDone", int(actionIdx)),
        "dependency not satisfied"
    )
}

/**
 * Vyper payoff function.
 * SEMANTIC: Identical terminal payoff distribution.
 */
private fun buildVyperPayoffFunction(g: GameIR): FunctionDecl {
    val body = buildList {
        // Inline at_final_phase checks
        add(vyAssert(
            selfIndex("actionDone", v("FINAL_ACTION")),
            "game not over"
        ))
        add(vyAssert(
            not(selfMember("payoffs_distributed")),
            "payoffs already sent"
        ))

        add(assign(selfMember("payoffs_distributed"), vyTrue))

        (g.roles + g.chanceRoles).forEach { role ->
            val payoffExpr = g.payoffs[role] ?: return@forEach

            val vyPayoff = translateIrExprAtTerminal(payoffExpr, role)
            val roleAddrExpr = selfMember(roleAddr(role))

            add(assign(selfIndex(BALANCE_MAPPING, roleAddrExpr), vyPayoff))
        }
    }

    return FunctionDecl(
        name = "distributePayoffs",
        params = emptyList(),
        decorators = listOf(Decorator.External),
        body = body
    )
}

/**
 * Withdraw function.
 * KEY DIFFERENCE: Vyper uses raw_call instead of .call{value:...}.
 */
private fun buildWithdraw(): FunctionDecl {
    return FunctionDecl(
        name = "withdraw",
        params = emptyList(),
        decorators = listOf(Decorator.External),
        body = listOf(
            varDecl(VyType.Int256, "bal", selfIndex(BALANCE_MAPPING, msgSender)),
            vyAssert(v("bal") gt int(0), "no funds"),
            assign(selfIndex(BALANCE_MAPPING, msgSender), int(0)),
            // CEI pattern: check-effects-interact
            // Fixed version (MontyHall.vy line 149 has a bug - missing ok assignment)
            varDecl(
                VyType.Bool,
                "ok",
                rawCall(
                    target = msgSender,
                    data = bytes(""),
                    value = convert(v("bal"), VyType.Uint256),
                    maxOutsize = 0,
                    gas = RAW_CALL_GAS_LIMIT
                )
            ),
            vyAssert(v("ok"), "ETH send failed")
        )
    )
}

/**
 * Default function (fallback).
 * Rejects direct ETH transfers.
 */
private fun buildDefaultFunction(): FunctionDecl {
    return FunctionDecl(
        name = "__default__",
        params = emptyList(),
        decorators = listOf(Decorator.Payable, Decorator.External),
        body = listOf(
            vyAssert(vyFalse, "direct ETH not allowed")
        )
    )
}

/* ====================== IR->Vyper translation atoms ====================== */

/**
 * SEMANTIC: Type translation is identical to Solidity.
 */
internal fun translateType(t: Type): VyType = when (t) {
    is Type.IntType -> VyType.Int256
    is Type.BoolType -> VyType.Bool
    is Type.SetType -> VyType.Int256 // Enums/sets are represented as integers
}

/**
 * SEMANTIC: Expression translation logic is identical to Solidity.
 * Only syntactic difference is the output type (VyExpr vs SolExpr).
 *
 * Translates a vegas.ir.Expr into a vegas.backend.vyper.VyExpr.
 */
internal fun translateIrExpr(
    expr: Expr,
    currentRole: RoleId,
    currentParams: List<ActionParam>,
    context: ExprContext
): VyExpr = when (expr) {
    // Literals
    is Expr.Const.IntVal  -> int(expr.v)
    is Expr.Const.BoolVal -> bool(expr.v)
    is Expr.Const.Hidden -> TODO("Hidden literal not yet supported")
    Expr.Const.Opaque -> TODO("Opaque literal not yet supported")
    Expr.Const.Quit -> TODO("Quit literal not yet supported")

    // Field access
    is Expr.Field -> {
        val (role, param) = expr.field

        // Is this field an input to the *current* action?
        val isInput =
            context == ExprContext.WHERE_CLAUSE &&
                    role == currentRole &&
                    currentParams.any { it.name == param }

        if (isInput) {
            // Read from function input
            v(inputParam(param, hidden = false))
        } else {
            // Read from storage (with self. prefix)
            selfMember(storageParam(role, param, hidden = false))
        }
    }

    // isDefined(field) -> use the clear done-flag
    is Expr.IsDefined -> {
        val (role, param) = expr.field
        selfMember(doneFlag(role, param, hidden = false))
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
    is Expr.Ite -> IfExpr(
        condition = translateIrExpr(expr.c, currentRole, currentParams, context),
        ifTrue   = translateIrExpr(expr.t, currentRole, currentParams, context),
        ifFalse  = translateIrExpr(expr.e, currentRole, currentParams, context)
    )
}

/**
 * SEMANTIC: Domain guard generation is identical to Solidity.
 */
internal fun translateDomainGuards(params: List<ActionParam>): List<Statement.Assert> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = v(inputParam(p.name, false))
                    val cond = t.values.map { x eq int(it) }.reduce<VyExpr, VyExpr> { a, b -> a or b }
                    vyAssert(cond, "domain")
                }
            }
            else -> null
        }
    }

/**
 * SEMANTIC: Assignment generation is identical to Solidity.
 */
private fun translateAssignments(role: RoleId, params: List<ActionParam>): List<Statement.Assign> =
    params.flatMap { p ->
        val storage = selfMember(storageParam(role, p.name, false))
        val input = v(inputParam(p.name, false))
        val done = selfMember(doneFlag(role, p.name, false))
        listOf(assign(storage, input), assign(done, vyTrue))
    }

/**
 * SEMANTIC: Where clause translation is identical to Solidity.
 */
private fun translateWhere(
    expr: Expr,
    role: RoleId,
    currentParams: List<ActionParam>
): List<Statement.Assert> {
    // Don't emit a trivial `assert True`
    if (expr == Expr.Const.BoolVal(true)) return emptyList()

    val vyCondition = translateIrExpr(
        expr          = expr,
        currentRole   = role,
        currentParams = currentParams,
        context       = ExprContext.WHERE_CLAUSE
    )
    return listOf(vyAssert(vyCondition, "where"))
}

/**
 * Translate a payoff expression at the terminal configuration.
 * SEMANTIC: Identical to Solidity.
 */
private fun translateIrExprAtTerminal(
    expr: Expr,
    role: RoleId
): VyExpr =
    translateIrExpr(
        expr          = expr,
        currentRole   = role,
        currentParams = emptyList(),
        context       = ExprContext.PAYOFF
    )

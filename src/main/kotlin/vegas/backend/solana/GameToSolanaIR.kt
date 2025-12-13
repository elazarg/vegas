package vegas.backend.solana

import vegas.RoleId
import vegas.FieldRef
import vegas.VarId
import vegas.ir.*
import vegas.backend.solana.SolanaExpr.*
import vegas.backend.solana.SolanaStmt.*
import vegas.backend.solana.SolanaType.*

fun compileToSolana(game: GameIR): SolanaProgram {
    val rolesSorted = (game.roles + game.chanceRoles).sortedBy { it.name }
    val roleMap = rolesSorted.mapIndexed { index, role -> role to index }.toMap()

    val dag = game.dag
    val linearization = linearizeDag(dag)

    val stateStruct = buildStateStruct(game, dag, linearization, rolesSorted)
    val errors = buildErrors()

    val instructions = buildInstructions(game, dag, linearization, rolesSorted, roleMap)

    return SolanaProgram(
        name = game.name,
        stateStruct = stateStruct,
        errors = errors,
        instructions = instructions,
        additionalStructs = emptyList()
    )
}

// =========================================================================
// 1. Linearization & Helpers
// =========================================================================

private fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.topo()
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()

private fun getRoleIndex(role: RoleId, roleMap: Map<RoleId, Int>): Int =
    roleMap[role] ?: error("Unknown role $role")

// =========================================================================
// 2. State Struct
// =========================================================================

private fun buildStateStruct(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    roles: List<RoleId>
): SolanaAccountStruct {
    val fields = mutableListOf<SolanaField>()

    val nRoles = roles.size
    val nActions = linearization.size

    // Core state
    fields.add(SolanaField("game_id", U64))
    fields.add(SolanaField("roles", Array(Pubkey, nRoles)))
    fields.add(SolanaField("joined", Array(Bool, nRoles)))
    fields.add(SolanaField("last_ts", I64))
    fields.add(SolanaField("bailed", Array(Bool, nRoles)))
    fields.add(SolanaField("action_done", Array(Bool, nActions)))
    fields.add(SolanaField("action_ts", Array(I64, nActions)))
    fields.add(SolanaField("timeout", I64))
    fields.add(SolanaField("pot_total", U64))
    fields.add(SolanaField("is_finalized", Bool))
    fields.add(SolanaField("claimed", Array(Bool, nRoles)))
    fields.add(SolanaField("claim_amount", Array(U64, nRoles)))

    // Game Variables
    val visited = mutableSetOf<FieldRef>()
    dag.metas.forEach { meta ->
        meta.struct.visibility.forEach { (field, vis) ->
            if (!visited.add(field)) return@forEach

            val paramType = meta.spec.params.find { it.name == field.param }?.type ?: Type.IntType
            val solType = translateType(paramType)

            // Clear value
            fields.add(SolanaField(storageName(field.owner, field.param, false), solType))
            fields.add(SolanaField(doneFlagName(field.owner, field.param, false), Bool))

            // Commitment (Hidden)
            if (vis == Visibility.COMMIT) {
                // Commitment is 32 bytes hash
                fields.add(SolanaField(storageName(field.owner, field.param, true), Array(U8, 32)))
                fields.add(SolanaField(doneFlagName(field.owner, field.param, true), Bool))
            }
        }
    }

    return SolanaAccountStruct("GameState", fields)
}

private fun buildErrors(): List<SolanaError> {
    return listOf(
        SolanaError("NotJoined", "Player has not joined"),
        SolanaError("AlreadyJoined", "Player already joined"),
        SolanaError("Unauthorized", "Signer is not the authorized player"),
        SolanaError("Timeout", "Action timed out"),
        SolanaError("DependencyNotMet", "Action dependency not met"),
        SolanaError("InvalidReveal", "Reveal hash mismatch"),
        SolanaError("AlreadyDone", "Action already performed"),
        SolanaError("AlreadyClaimed", "Funds already claimed"),
        SolanaError("NotFinalized", "Game not finalized"),
        SolanaError("BadAmount", "Invalid amount"),
        SolanaError("GuardFailed", "Guard condition failed")
    )
}

// =========================================================================
// 3. Instructions
// =========================================================================

private fun buildInstructions(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    roles: List<RoleId>,
    roleMap: Map<RoleId, Int>
): List<SolanaInstruction> {
    val list = mutableListOf<SolanaInstruction>()

    list.add(buildInitInstruction())

    dag.topo().forEach { id ->
        list.add(buildActionInstruction(id, dag, linearization, roleMap))
    }

    list.add(buildFinalizeInstruction(g, dag, linearization, roles, roleMap))

    roles.forEach { role ->
        list.add(buildClaimInstruction(role, roleMap[role]!!))
    }

    return list
}

private fun buildInitInstruction(): SolanaInstruction {
    return SolanaInstruction(
        name = "init_instance",
        accounts = listOf(
            SolanaAccountMeta("game", "Account<'info, GameState>", isMut = true, constraints = listOf(
                "#[account(init, payer = signer, space = 8 + 10240, seeds = [b\"game\", game_id.to_le_bytes().as_ref()], bump)]"
            )),
            SolanaAccountMeta("vault", "SystemAccount<'info>", isMut = true, constraints = listOf(
                "#[account(init, payer = signer, space = 8, seeds = [b\"vault\", game.key().as_ref()], bump)]"
            )),
            SolanaAccountMeta("signer", "Signer<'info>", isMut = true),
            SolanaAccountMeta("system_program", "Program<'info, System>")
        ),
        params = listOf(SolanaParam("game_id", U64), SolanaParam("timeout", I64)),
        body = listOf(
            Assign(FieldAccess(Var("game"), "game_id"), Var("game_id")),
            Assign(FieldAccess(Var("game"), "timeout"), Var("timeout")),
            Assign(FieldAccess(Var("game"), "last_ts"), ClockTimestamp),
            Assign(FieldAccess(Var("game"), "pot_total"), IntLit(0)),
        )
    )
}

private fun emitCheckTimestamp(roleIdx: Int): List<SolanaStmt> {
    return listOf(
        SolanaStmt.If(
            Binary(BinaryOp.GT, ClockTimestamp, Binary(BinaryOp.ADD, FieldAccess(Var("game"), "last_ts"), FieldAccess(Var("game"), "timeout"))),
            listOf(
                Assign(Index(FieldAccess(Var("game"), "bailed"), IntLit(roleIdx.toLong())), BoolLit(true)),
                Assign(FieldAccess(Var("game"), "last_ts"), ClockTimestamp)
            )
        )
    )
}

private fun buildActionInstruction(
    id: ActionId,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    roleMap: Map<RoleId, Int>
): SolanaInstruction {
    val meta = dag.meta(id)
    val idx = linearization.getValue(id)
    val spec = meta.spec
    val struct = meta.struct
    val roleIdx = roleMap[meta.struct.owner]!!

    val params = mutableListOf<SolanaParam>()
    spec.params.forEach { p ->
        if (meta.kind == Visibility.COMMIT) {
             params.add(SolanaParam("hidden_${p.name}", Array(U8, 32)))
        } else {
             params.add(SolanaParam(p.name.name, translateType(p.type)))
        }
    }

    if (meta.kind == Visibility.REVEAL) {
        params.add(SolanaParam("salt", U64))
    }

    val accounts = mutableListOf<SolanaAccountMeta>()
    accounts.add(SolanaAccountMeta("game", "Account<'info, GameState>", isMut = true, constraints = listOf(
        "#[account(seeds = [b\"game\", game.game_id.to_le_bytes().as_ref()], bump)]"
    )))
    accounts.add(SolanaAccountMeta("signer", "Signer<'info>", isMut = true))

    val hasDeposit = (spec.join?.deposit?.v ?: 0) > 0
    if (hasDeposit) {
        accounts.add(SolanaAccountMeta("vault", "SystemAccount<'info>", isMut = true, constraints = listOf(
             "#[account(seeds = [b\"vault\", game.key().as_ref()], bump)]"
        )))
        accounts.add(SolanaAccountMeta("system_program", "Program<'info, System>"))
    }

    val body = mutableListOf<SolanaStmt>()

    // 1. Role Check
    if (spec.join != null) {
        body.add(Require(Unary(UnaryOp.NOT, Index(FieldAccess(Var("game"), "joined"), IntLit(roleIdx.toLong()))), SolanaError("AlreadyJoined", "Already joined")))
        body.add(Assign(Index(FieldAccess(Var("game"), "roles"), IntLit(roleIdx.toLong())), MethodCall(Var("signer"), "key", emptyList())))
        body.add(Assign(Index(FieldAccess(Var("game"), "joined"), IntLit(roleIdx.toLong())), BoolLit(true)))

        val deposit = spec.join.deposit.v.toLong()
        if (deposit > 0) {
             body.add(SolanaStmt.Comment("Deposit $deposit lamports"))
             body.add(SolanaStmt.TransferSol(from = "signer", to = "vault", amount = IntLit(deposit)))
             body.add(Assign(FieldAccess(Var("game"), "pot_total"), Binary(BinaryOp.ADD, FieldAccess(Var("game"), "pot_total"), IntLit(deposit))))
        }
    } else {
        body.add(Require(Binary(BinaryOp.EQ, Index(FieldAccess(Var("game"), "roles"), IntLit(roleIdx.toLong())), MethodCall(Var("signer"), "key", emptyList())), SolanaError("Unauthorized", "Unauthorized")))
    }

    // 2. Timeout Check (Actor)
    body.addAll(emitCheckTimestamp(roleIdx))
    // require!(!game.bailed[roleIdx], Timeout)
    body.add(Require(Unary(UnaryOp.NOT, Index(FieldAccess(Var("game"), "bailed"), IntLit(roleIdx.toLong()))), SolanaError("Timeout", "Action timed out")))

    // 3. One-Shot Check
    body.add(Require(Unary(UnaryOp.NOT, Index(FieldAccess(Var("game"), "action_done"), IntLit(idx.toLong()))), SolanaError("AlreadyDone", "Action already performed")))

    // 4. Dependency Checks
    dag.prerequisitesOf(id).forEach { pred ->
        val predIdx = linearization.getValue(pred)
        val predOwner = roleMap[dag.owner(pred)]!!

        // Check timeout for dependency owner
        body.addAll(emitCheckTimestamp(predOwner))

        body.add(SolanaStmt.If(
            Unary(UnaryOp.NOT, Index(FieldAccess(Var("game"), "bailed"), IntLit(predOwner.toLong()))),
            listOf(Require(
                Index(FieldAccess(Var("game"), "action_done"), IntLit(predIdx.toLong())),
                SolanaError("DependencyNotMet", "Dependency not met")
            ))
        ))
    }

    // 5. Guards
    if (meta.kind != Visibility.COMMIT) {
        val guards = translateDomainGuards(spec.params) + if (spec.guardExpr != Expr.Const.BoolVal(true)) {
            listOf(translateExpr(spec.guardExpr, meta.struct.owner, spec.params.map { it.name.name }.toSet()))
        } else emptyList()

        if (guards.isNotEmpty()) {
             val combinedGuard = guards.reduce { a, b -> Binary(BinaryOp.AND, a, b) }
             body.add(Require(combinedGuard, SolanaError("GuardFailed", "Guard failed")))
        }
    }

    // 6. Updates
    spec.params.forEach { p ->
        val inputName = if (meta.kind == Visibility.COMMIT) "hidden_${p.name}" else p.name.name
        val storage = storageName(struct.owner, p.name, meta.kind == Visibility.COMMIT)
        val done = doneFlagName(struct.owner, p.name, meta.kind == Visibility.COMMIT)

        if (meta.kind == Visibility.REVEAL) {
             val commitStorage = storageName(struct.owner, p.name, true)
             val cast = if (p.type is Type.BoolType) " as u8" else ""
             body.add(SolanaStmt.Code("""
                 {
                     let val_bytes = ($inputName$cast).to_le_bytes();
                     let salt_bytes = salt.to_le_bytes();
                     let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
                     require!(hash == game.$commitStorage, ErrorCode::InvalidReveal);
                 }
             """.trimIndent()))
        }

        if (meta.kind == Visibility.COMMIT) {
             body.add(Assign(FieldAccess(Var("game"), storage), Var(inputName)))
        } else {
             body.add(Assign(FieldAccess(Var("game"), storage), Var(inputName)))
        }

        body.add(Assign(FieldAccess(Var("game"), done), BoolLit(true)))
    }

    // Action Done
    body.add(Assign(Index(FieldAccess(Var("game"), "action_done"), IntLit(idx.toLong())), BoolLit(true)))
    body.add(Assign(Index(FieldAccess(Var("game"), "action_ts"), IntLit(idx.toLong())), ClockTimestamp))
    body.add(Assign(FieldAccess(Var("game"), "last_ts"), ClockTimestamp))

    return SolanaInstruction(
        name = "move_${meta.struct.owner.name}_$idx",
        accounts = accounts,
        params = params,
        body = body
    )
}

private fun buildFinalizeInstruction(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    roles: List<RoleId>,
    roleMap: Map<RoleId, Int>
): SolanaInstruction {
    val body = mutableListOf<SolanaStmt>()

    dag.sinks().forEach { sink ->
        val idx = linearization.getValue(sink)
        val owner = roleMap[dag.owner(sink)]!!
        body.add(Require(
            Binary(BinaryOp.OR, Index(FieldAccess(Var("game"), "action_done"), IntLit(idx.toLong())), Index(FieldAccess(Var("game"), "bailed"), IntLit(owner.toLong()))),
             SolanaError("NotFinalized", "Not finalized")
        ))
    }

    var totalPayout: SolanaExpr = IntLit(0)
    val payoutVars = mutableMapOf<RoleId, String>()

    g.payoffs.forEach { (role, expr) ->
        val varName = "p_${role.name}"
        payoutVars[role] = varName
        val valExpr = translateExpr(expr, null, emptySet())
        body.add(Let(varName, U64, Raw("(std::cmp::max(0, ${generateExpr(valExpr)})) as u64")))
        totalPayout = Binary(BinaryOp.ADD, totalPayout, Var(varName))
    }

    body.add(SolanaStmt.If(
        Binary(BinaryOp.GT, totalPayout, FieldAccess(Var("game"), "pot_total")),
        roles.map { role ->
             val deposit = dag.deposit(role).v.toLong()
             Assign(Index(FieldAccess(Var("game"), "claim_amount"), IntLit(roleMap[role]!!.toLong())), IntLit(deposit))
        },
        roles.map { role ->
             Assign(Index(FieldAccess(Var("game"), "claim_amount"), IntLit(roleMap[role]!!.toLong())), Var(payoutVars[role]!!))
        }
    ))

    body.add(Assign(FieldAccess(Var("game"), "is_finalized"), BoolLit(true)))

    return SolanaInstruction(
        name = "finalize",
        accounts = listOf(SolanaAccountMeta("game", "Account<'info, GameState>", isMut = true)),
        params = emptyList(),
        body = body
    )
}

private fun buildClaimInstruction(role: RoleId, roleIdx: Int): SolanaInstruction {
    val body = mutableListOf<SolanaStmt>()

    body.add(Require(FieldAccess(Var("game"), "is_finalized"), SolanaError("NotFinalized", "Not finalized")))
    body.add(Require(Unary(UnaryOp.NOT, Index(FieldAccess(Var("game"), "claimed"), IntLit(roleIdx.toLong()))), SolanaError("AlreadyClaimed", "Already claimed")))

    body.add(Assign(Index(FieldAccess(Var("game"), "claimed"), IntLit(roleIdx.toLong())), BoolLit(true)))

    val roleName = role.name
    body.add(SolanaStmt.Code("""
        {
            let amount = game.claim_amount[$roleIdx];
            if amount > 0 {
                let seeds = &[
                    b"vault",
                    game.to_account_info().key.as_ref(),
                    &[ctx.bumps.vault],
                ];
                let signer_seeds = &[&seeds[..]];
                anchor_lang::system_program::transfer(
                    anchor_lang::context::CpiContext::new_with_signer(
                        ctx.accounts.system_program.to_account_info(),
                        anchor_lang::system_program::Transfer {
                            from: ctx.accounts.vault.to_account_info(),
                            to: ctx.accounts.signer.to_account_info(),
                        },
                        signer_seeds
                    ),
                    amount,
                )?;
            }
        }
    """.trimIndent()))

    return SolanaInstruction(
        name = "claim_${roleName}",
        accounts = listOf(
            SolanaAccountMeta("game", "Account<'info, GameState>", isMut = true),
            SolanaAccountMeta("vault", "SystemAccount<'info>", isMut = true, constraints = listOf(
                "#[account(seeds = [b\"vault\", game.key().as_ref()], bump)]"
            )),
            SolanaAccountMeta("signer", "Signer<'info>", isMut = true, constraints = listOf(
                "#[account(constraint = signer.key() == game.roles[$roleIdx] @ ErrorCode::Unauthorized)]"
            )),
            SolanaAccountMeta("system_program", "Program<'info, System>")
        ),
        params = emptyList(),
        body = body
    )
}

// =========================================================================
// Helpers
// =========================================================================

private fun storageName(role: RoleId, param: VarId, hidden: Boolean): String =
    if (hidden) "${role.name}_${param}_hidden"
    else "${role.name}_${param}"

private fun doneFlagName(role: RoleId, param: VarId, hidden: Boolean): String {
    return "done_${storageName(role, param, hidden)}"
}

private fun translateType(t: Type): SolanaType = when (t) {
    is Type.IntType -> I64
    is Type.BoolType -> Bool
    is Type.SetType -> I64
}

private fun translateDomainGuards(params: List<ActionParam>): List<SolanaExpr> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = Var(p.name.name) // Input param
                    t.values.map { Binary(BinaryOp.EQ, x, IntLit(it.toLong())) }
                        .reduce<SolanaExpr, SolanaExpr> { a, b -> Binary(BinaryOp.OR, a, b) }
                }
            }
            else -> null
        }
    }

private fun translateExpr(
    expr: Expr,
    contextOwner: RoleId?,
    contextParams: Set<String>
): SolanaExpr = when (expr) {
    is Expr.Const.IntVal -> IntLit(expr.v.toLong())
    is Expr.Const.BoolVal -> BoolLit(expr.v)
    is Expr.Const.Hidden -> error("Hidden constants should be resolved")
    is Expr.Const.Opaque -> error("Opaque constants not supported")
    is Expr.Const.Quit -> error("Quit not supported")

    is Expr.Field -> {
        val (role, name) = expr.field
        if (contextOwner == role && name.name in contextParams) {
             Var(name.name)
        } else {
             FieldAccess(Var("game"), storageName(role, name, false))
        }
    }
    is Expr.IsDefined -> {
        val (role, name) = expr.field
        FieldAccess(Var("game"), doneFlagName(role, name, false))
    }

    is Expr.Add -> Binary(BinaryOp.ADD, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Sub -> Binary(BinaryOp.SUB, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Mul -> Binary(BinaryOp.MUL, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Div -> Binary(BinaryOp.DIV, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Mod -> Binary(BinaryOp.MOD, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Neg -> Unary(UnaryOp.NEG, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Eq -> Binary(BinaryOp.EQ, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Ne -> Binary(BinaryOp.NE, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Lt -> Binary(BinaryOp.LT, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Le -> Binary(BinaryOp.LE, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Gt -> Binary(BinaryOp.GT, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Ge -> Binary(BinaryOp.GE, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))

    is Expr.And -> Binary(BinaryOp.AND, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Or -> Binary(BinaryOp.OR, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Not -> Unary(UnaryOp.NOT, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Ite -> SolanaExpr.If(
        translateExpr(expr.c, contextOwner, contextParams),
        translateExpr(expr.t, contextOwner, contextParams),
        translateExpr(expr.e, contextOwner, contextParams)
    )
}

// Helper to generate string for Code blocks
private fun generateExpr(expr: SolanaExpr): String {
     return generateAnchorExpr(expr)
}

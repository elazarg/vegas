package vegas.backend.move

import vegas.RoleId
import vegas.FieldRef
import vegas.VarId
import vegas.ir.*

fun compileToMove(game: GameIR, platform: MovePlatform): MovePackage {
    val dag = game.dag
    val linearization = linearizeDag(dag)

    // Build the main module
    val moduleName = game.name.lowercase()
    val instanceStruct = buildInstanceStruct(game, dag, platform)

    val functions = buildList {
        add(buildInitFunction(platform))
        add(buildCreateGameFunction(game, instanceStruct, platform))

        // Join functions
        game.roles.forEach { role ->
            add(buildJoinFunction(role, game, platform))
        }

        // Move functions
        dag.topo().forEach { actionId ->
            add(buildActionFunction(actionId, dag, linearization, platform))
        }

        // Finalize
        add(buildFinalizeFunction(game, dag, platform))

        // Claim
        game.roles.forEach { role ->
            add(buildClaimFunction(role, game, platform))
        }
    }

    val module = MoveModule(
        name = moduleName,
        imports = platform.imports,
        structs = listOf(instanceStruct),
        functions = functions
    )

    return MovePackage(
        name = game.name,
        modules = listOf(module)
    )
}

// ==========================================
// Helpers
// ==========================================

private fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.topo()
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()

// Names
fun instanceName() = "Instance"
fun roleAddrName(role: RoleId) = "role_${role.name}"
fun roleJoinedName(role: RoleId) = "joined_${role.name}"
fun roleBailedName(role: RoleId) = "bailed_${role.name}"
fun roleClaimedName(role: RoleId) = "claimed_${role.name}"
fun roleClaimAmountName(role: RoleId) = "claim_amount_${role.name}"

fun fieldName(role: RoleId, param: VarId, hidden: Boolean): String =
    if (hidden) "${role.name}_${param}_hidden" else "${role.name}_${param}"

fun doneFlagName(role: RoleId, param: VarId, hidden: Boolean): String =
    "done_${fieldName(role, param, hidden)}"

fun inputParamName(param: VarId, hidden: Boolean): String =
    if (hidden) "hidden_${param.name}" else param.name

// ==========================================
// Struct Building
// ==========================================

private fun buildInstanceStruct(game: GameIR, dag: ActionDag, platform: MovePlatform): MoveStruct {
    val fields = buildList {
        addAll(platform.extraInstanceFields(game))

        // Roles
        game.roles.forEach { role ->
            add(MoveField(roleAddrName(role), platform.addressType()))
        }

        game.roles.forEach { role ->
            add(MoveField(roleJoinedName(role), platform.boolType()))
        }

        add(MoveField("timeout_ms", platform.u64Type()))
        add(MoveField("last_ts_ms", platform.u64Type()))

        game.roles.forEach { role ->
            add(MoveField(roleBailedName(role), platform.boolType()))
        }

        add(MoveField("pot", platform.balanceType(MoveType.TypeParam("Asset"))))

        add(MoveField("finalized", platform.boolType()))

        game.roles.forEach { role ->
            add(MoveField(roleClaimAmountName(role), platform.u64Type()))
            add(MoveField(roleClaimedName(role), platform.boolType()))
        }

        // Game fields
        val visited = mutableSetOf<FieldRef>()
        dag.metas.forEach { meta ->
            meta.struct.visibility.forEach { (field, vis) ->
                if (!visited.add(field)) return@forEach

                val paramType = meta.spec.params.find { it.name == field.param }?.type ?: Type.IntType
                val moveType = translateType(paramType, platform)

                // Clear value
                add(MoveField(fieldName(field.owner, field.param, false), moveType))
                add(MoveField(doneFlagName(field.owner, field.param, false), platform.boolType()))

                // Commit value
                if (vis == Visibility.COMMIT) {
                    add(MoveField(fieldName(field.owner, field.param, true), MoveType.Vector(MoveType.U8)))
                    add(MoveField(doneFlagName(field.owner, field.param, true), platform.boolType()))
                }
            }
        }

        // Action Done flags
        dag.topo().forEach { actionId ->
            add(MoveField("action_${actionId.first.name}_${actionId.second}_done", platform.boolType()))
        }
    }

    return MoveStruct(
        name = instanceName(),
        abilities = platform.instanceAbilities(),
        fields = fields,
        typeParams = listOf("phantom Asset")
    )
}

// ==========================================
// Function Building
// ==========================================

private fun buildInitFunction(platform: MovePlatform): MoveFunction {
    return MoveFunction(
        name = "init",
        visibility = MoveVisibility.PRIVATE,
        params = platform.initFunctionParams(),
        body = emptyList()
    )
}

private fun buildCreateGameFunction(game: GameIR, struct: MoveStruct, platform: MovePlatform): MoveFunction {
    val ctxVar = MoveExpr.Var(platform.contextParamName())
    val instanceVar = MoveExpr.Var("instance")

    val body = buildList {
        val extraInits = platform.extraInstanceInit(ctxVar)

        // Build instance
        val fields = struct.fields.map { field ->
            val value: MoveExpr = extraInits[field.name] ?: when(field.name) {
                "timeout_ms" -> MoveExpr.Var("timeout_ms")
                "last_ts_ms" -> MoveExpr.U64Lit(0)
                "pot" -> platform.zeroBalance(MoveType.TypeParam("Asset"))
                "finalized" -> MoveExpr.BoolLit(false)
                else -> {
                    if (field.type == platform.boolType()) MoveExpr.BoolLit(false)
                    else if (field.type == platform.u64Type()) MoveExpr.U64Lit(0)
                    else if (field.type == platform.addressType()) MoveExpr.AddressLit("0x0")
                    else if (field.type is MoveType.Vector) MoveExpr.Call("vector", "empty", listOf((field.type as MoveType.Vector).param), emptyList())
                    else error("Unknown field init for ${field.name}")
                }
            }
            MoveFieldInit(field.name, value)
        }

        add(MoveStmt.Let("instance", null, MoveExpr.StructInit(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), fields)))

        addAll(platform.createInstanceBody(ctxVar, instanceVar, MoveType.TypeParam("Asset")))
    }

    return MoveFunction(
        name = "create_game",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("timeout_ms", platform.u64Type()),
            MoveParam(platform.contextParamName(), platform.contextParamType(true))
        ),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildJoinFunction(role: RoleId, game: GameIR, platform: MovePlatform): MoveFunction {
    val body = buildList {
        val roleJoined = roleJoinedName(role)
        val roleAddr = roleAddrName(role)
        val ctxVar = MoveExpr.Var(platform.contextParamName())
        val clockVar = platform.extraActionParams().find { it.name == "clock" }?.let { MoveExpr.Var(it.name) }
        val deposit = try { game.dag.deposit(role).v } catch (e: Exception) { 0 }

        add(MoveStmt.Assert(
            MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleJoined)),
            100
        ))

        if (deposit > 0) {
            add(MoveStmt.Assert(
                MoveExpr.BinOp(MoveBinOp.EQ,
                    platform.coinValue(MoveExpr.Var("payment"), MoveType.TypeParam("Asset")),
                    MoveExpr.U64Lit(deposit.toLong())
                ),
                112 // EBadDeposit
            ))
        }

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleAddr),
            platform.getSender(ctxVar)
        ))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleJoined),
            MoveExpr.BoolLit(true)
        ))

        add(platform.joinBalanceStmt(
             MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), true),
             MoveExpr.Var("payment"),
             MoveType.TypeParam("Asset")
        ))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
            platform.currentTimeExpr(clockVar)
        ))
    }

    return MoveFunction(
        name = "join_${role.name}",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)),
            MoveParam("payment", platform.coinType(MoveType.TypeParam("Asset"))),
        ) + platform.extraActionParams() + listOf(MoveParam(platform.contextParamName(), platform.contextParamType(true))),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildActionFunction(
    id: ActionId,
    dag: ActionDag,
    linearization: Map<ActionId, Int>,
    platform: MovePlatform
): MoveFunction {
    val meta = dag.meta(id)
    val idx = linearization.getValue(id)
    val struct = meta.struct
    val spec = meta.spec
    val kind = meta.kind
    val hidden = kind == Visibility.COMMIT

    val params = buildList {
        add(MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)))
        addAll(platform.extraActionParams())
        add(MoveParam(platform.contextParamName(), platform.contextParamType(true)))

        spec.params.forEach { p ->
            val type = if (hidden) MoveType.Vector(MoveType.U8) else translateType(p.type, platform)
            val varName = inputParamName(p.name, hidden)
            add(MoveParam(varName, type))
        }

        if (kind == Visibility.REVEAL) {
            add(MoveParam("salt", platform.u64Type()))
        }
    }

    val body = buildList {
        val owner = struct.owner
        val ctxVar = MoveExpr.Var(platform.contextParamName())
        val clockVar = platform.extraActionParams().find { it.name == "clock" }?.let { MoveExpr.Var(it.name) }

        // 1. Auth & Liveness
        add(MoveStmt.Assert(
            platform.checkSender(ctxVar, MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleAddrName(owner))),
            101
        ))

        // Ensure joined
        add(MoveStmt.Assert(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleJoinedName(owner)),
            113 // ENotJoined
        ))

        // Ensure not bailed (EVM-style: bailed roles cannot act)
        add(MoveStmt.Assert(
            MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleBailedName(owner))),
            114 // EPlayerBailed
        ))

        val now = platform.currentTimeExpr(clockVar)

        // Timeout check (Self-bail)
        add(MoveStmt.If(
            MoveExpr.BinOp(MoveBinOp.GT, now, MoveExpr.BinOp(MoveBinOp.ADD,
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "timeout_ms")
            )),
            listOf(
                MoveStmt.Assign(
                    MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleBailedName(owner)),
                    MoveExpr.BoolLit(true)
                ),
                MoveStmt.Return(null) // Return early if bailed
            )
        ))

        val actionDoneField = "action_${id.first.name}_${id.second}_done"
        add(MoveStmt.Assert(
            MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), actionDoneField)),
            102
        ))

        // Deps: Require done OR (dep_owner is bailed)
        dag.prerequisitesOf(id).forEach { depId ->
            val depDoneField = "action_${depId.first.name}_${depId.second}_done"
            val depOwner = dag.owner(depId)
            val depBailed = MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleBailedName(depOwner))

            add(MoveStmt.Assert(
                MoveExpr.BinOp(MoveBinOp.OR,
                    MoveExpr.FieldAccess(MoveExpr.Var("instance"), depDoneField),
                    depBailed
                ),
                103
            ))
        }

        if (!hidden) {
             val guards = translateDomainGuards(spec.params, platform)
             guards.forEach { g ->
                 add(MoveStmt.Assert(g, 104))
             }

             if (spec.guardExpr != Expr.Const.BoolVal(true)) {
                 val guard = translateExpr(
                     spec.guardExpr,
                     contextOwner = owner,
                     contextParams = spec.params.map { it.name }.toSet(),
                     platform = platform
                 )
                 add(MoveStmt.Assert(guard, 105))
             }
        }

        // 32-byte constraint for commits
        if (hidden) {
            spec.params.forEach { p ->
                val input = MoveExpr.Var(inputParamName(p.name, hidden))
                add(MoveStmt.Assert(
                    MoveExpr.BinOp(MoveBinOp.EQ,
                        MoveExpr.Call("vector", "length", listOf(MoveType.U8), listOf(MoveExpr.Borrow(input, false))),
                        MoveExpr.U64Lit(32)
                    ),
                    115 // EInvalidCommitLength
                ))
            }
        }

        if (kind == Visibility.REVEAL) {
             spec.params.forEach { p ->
                 val input = MoveExpr.Var(inputParamName(p.name, false))
                 val salt = MoveExpr.Var("salt")

                 add(MoveStmt.Let("data_${p.name}", null, MoveExpr.Call("bcs", "to_bytes", listOf(translateType(p.type, platform)), listOf(
                     MoveExpr.Borrow(input, false)
                 )), mut = true)) // MUTABLE

                 add(MoveStmt.ExprStmt(MoveExpr.Call("vector", "append", listOf(MoveType.U8), listOf(
                     MoveExpr.Borrow(MoveExpr.Var("data_${p.name}"), true),
                     MoveExpr.Call("bcs", "to_bytes", listOf(platform.u64Type()), listOf(
                         MoveExpr.Borrow(salt, false)
                     ))
                 ))))

                 val hash = platform.hash(MoveExpr.Borrow(MoveExpr.Var("data_${p.name}"), false))

                 val commitment = MoveExpr.FieldAccess(MoveExpr.Var("instance"), fieldName(owner, p.name, true))
                 add(MoveStmt.Assert(
                     MoveExpr.BinOp(MoveBinOp.EQ, hash, commitment),
                     106
                 ))
             }
        }

        spec.params.forEach { p ->
            val targetField = fieldName(owner, p.name, hidden)
            val doneField = doneFlagName(owner, p.name, hidden)
            val varName = inputParamName(p.name, hidden)

            add(MoveStmt.Assign(
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), targetField),
                MoveExpr.Var(varName)
            ))
            add(MoveStmt.Assign(
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), doneField),
                MoveExpr.BoolLit(true)
            ))
        }

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), actionDoneField),
            MoveExpr.BoolLit(true)
        ))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
            now
        ))
    }

    return MoveFunction(
        name = "move_${struct.owner.name}_$idx",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = params,
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildFinalizeFunction(game: GameIR, dag: ActionDag, platform: MovePlatform): MoveFunction {
    val body = buildList {
        val clockVar = platform.extraActionParams().find { it.name == "clock" }?.let { MoveExpr.Var(it.name) }
        val now = platform.currentTimeExpr(clockVar)

        val sinksDone = dag.sinks().map { sinkId ->
            val doneField = "action_${sinkId.first.name}_${sinkId.second}_done"
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), doneField)
        }.reduce<MoveExpr, MoveExpr> { a, b -> MoveExpr.BinOp(MoveBinOp.AND, a, b) }

        val timedOut = MoveExpr.BinOp(MoveBinOp.GT, now, MoveExpr.BinOp(MoveBinOp.ADD,
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "timeout_ms")
        ))

        // Assert sinks done OR timed out
        add(MoveStmt.Assert(
            MoveExpr.BinOp(MoveBinOp.OR, sinksDone, timedOut),
            107
        ))

        add(MoveStmt.Assert(MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), "finalized")), 108))

        add(MoveStmt.Let("total_payout", platform.u64Type(), MoveExpr.U64Lit(0), mut = true)) // MUTABLE

        game.payoffs.forEach { (role, expr) ->
            val payoutExpr = translateExpr(expr, null, emptySet(), platform)
            add(MoveStmt.Assign(
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleClaimAmountName(role)),
                payoutExpr
            ))
            add(MoveStmt.Assign(
                MoveExpr.Var("total_payout"),
                MoveExpr.BinOp(MoveBinOp.ADD, MoveExpr.Var("total_payout"), payoutExpr)
            ))
        }

        add(MoveStmt.Assert(
            MoveExpr.BinOp(MoveBinOp.LTE,
                MoveExpr.Var("total_payout"),
                MoveExpr.Call("balance", "value", listOf(MoveType.TypeParam("Asset")), listOf(MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), false)))
            ),
            109
        ))

        add(MoveStmt.Assign(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "finalized"), MoveExpr.BoolLit(true)))
    }

    return MoveFunction(
        name = "finalize",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
             MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)),
        ) + platform.extraActionParams() + listOf(MoveParam(platform.contextParamName(), platform.contextParamType(true))),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildClaimFunction(role: RoleId, game: GameIR, platform: MovePlatform): MoveFunction {
    val body = buildList {
        add(MoveStmt.Assert(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "finalized"), 110))

        val claimedField = roleClaimedName(role)
        add(MoveStmt.Assert(MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), claimedField)), 111))

        add(MoveStmt.Assign(MoveExpr.FieldAccess(MoveExpr.Var("instance"), claimedField), MoveExpr.BoolLit(true)))

        val amountField = roleClaimAmountName(role)
        add(MoveStmt.Let("amount", platform.u64Type(), MoveExpr.FieldAccess(MoveExpr.Var("instance"), amountField)))

        add(MoveStmt.If(
            MoveExpr.BinOp(MoveBinOp.GT, MoveExpr.Var("amount"), MoveExpr.U64Lit(0)),
            platform.withdrawAndTransferStmt(
                MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), true),
                MoveExpr.Var("amount"),
                platform.getSender(MoveExpr.Var(platform.contextParamName())),
                MoveExpr.Var(platform.contextParamName()),
                MoveType.TypeParam("Asset")
            )
        ))
    }

    return MoveFunction(
        name = "claim_${role.name}",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)),
        ) + platform.extraActionParams() + listOf(MoveParam(platform.contextParamName(), platform.contextParamType(true))),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun translateType(t: Type, platform: MovePlatform): MoveType = when(t) {
    is Type.IntType -> platform.u64Type()
    is Type.BoolType -> platform.boolType()
    is Type.SetType -> platform.u64Type()
}

private fun translateDomainGuards(params: List<ActionParam>, platform: MovePlatform): List<MoveExpr> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = MoveExpr.Var(inputParamName(p.name, false))
                    t.values.map { MoveExpr.BinOp(MoveBinOp.EQ, x, MoveExpr.U64Lit(it.toLong())) }
                        .reduce<MoveExpr, MoveExpr> { a, b -> MoveExpr.BinOp(MoveBinOp.OR, a, b) }
                }
            }
            else -> null
        }
    }

private fun translateExpr(
    expr: Expr,
    contextOwner: RoleId?,
    contextParams: Set<VarId>,
    platform: MovePlatform
): MoveExpr = when (expr) {
    is Expr.Const.IntVal -> MoveExpr.U64Lit(expr.v.toLong())
    is Expr.Const.BoolVal -> MoveExpr.BoolLit(expr.v)
    is Expr.Const.Hidden -> error("Hidden constants should be resolved")
    is Expr.Const.Opaque -> error("Opaque constants not supported")
    is Expr.Const.Quit -> error("Quit not supported")

    is Expr.Field -> {
        val (role, name) = expr.field
        if (contextOwner == role && name in contextParams) {
             MoveExpr.Var(inputParamName(name, false))
        } else {
             MoveExpr.FieldAccess(MoveExpr.Var("instance"), fieldName(role, name, false))
        }
    }

    is Expr.IsDefined -> {
        val (role, name) = expr.field
        MoveExpr.FieldAccess(MoveExpr.Var("instance"), doneFlagName(role, name, false))
    }

    is Expr.Add -> MoveExpr.BinOp(MoveBinOp.ADD, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Sub -> MoveExpr.BinOp(MoveBinOp.SUB, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Mul -> MoveExpr.BinOp(MoveBinOp.MUL, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Div -> MoveExpr.BinOp(MoveBinOp.DIV, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Mod -> MoveExpr.BinOp(MoveBinOp.MOD, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))

    is Expr.Neg -> MoveExpr.UnaryOp(MoveUnaryOp.NEG, translateExpr(expr.x, contextOwner, contextParams, platform))

    is Expr.Eq -> MoveExpr.BinOp(MoveBinOp.EQ, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Ne -> MoveExpr.BinOp(MoveBinOp.NEQ, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Lt -> MoveExpr.BinOp(MoveBinOp.LT, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Le -> MoveExpr.BinOp(MoveBinOp.LTE, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Gt -> MoveExpr.BinOp(MoveBinOp.GT, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Ge -> MoveExpr.BinOp(MoveBinOp.GTE, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))

    is Expr.And -> MoveExpr.BinOp(MoveBinOp.AND, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Or -> MoveExpr.BinOp(MoveBinOp.OR, translateExpr(expr.l, contextOwner, contextParams, platform), translateExpr(expr.r, contextOwner, contextParams, platform))
    is Expr.Not -> MoveExpr.UnaryOp(MoveUnaryOp.NOT, translateExpr(expr.x, contextOwner, contextParams, platform))

    is Expr.Ite -> MoveExpr.IfElse(
        translateExpr(expr.c, contextOwner, contextParams, platform),
        translateExpr(expr.t, contextOwner, contextParams, platform),
        translateExpr(expr.e, contextOwner, contextParams, platform)
    )
}

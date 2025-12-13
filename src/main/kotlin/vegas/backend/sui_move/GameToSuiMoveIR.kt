package vegas.backend.sui_move

import vegas.RoleId
import vegas.FieldRef
import vegas.VarId
import vegas.ir.*

fun compileToSuiMove(game: GameIR): MovePackage {
    val dag = game.dag
    val linearization = linearizeDag(dag)

    // Build the main module
    val moduleName = game.name.lowercase()
    val instanceStruct = buildInstanceStruct(game, dag)

    val functions = buildList {
        add(buildInitFunction())
        add(buildCreateGameFunction(game, instanceStruct)) // "init_instance"

        // Join functions
        game.roles.forEach { role ->
            add(buildJoinFunction(role, game))
        }

        // Move functions
        dag.topo().forEach { actionId ->
            add(buildActionFunction(actionId, dag, linearization))
        }

        // Finalize
        add(buildFinalizeFunction(game, dag))

        // Claim
        game.roles.forEach { role ->
            add(buildClaimFunction(role, game))
        }
    }

    val imports = setOf(
        MoveImport("sui", "object"),
        MoveImport("sui", "transfer"),
        MoveImport("sui", "tx_context"),
        MoveImport("sui", "coin"),
        MoveImport("sui", "balance"),
        MoveImport("sui", "clock"),
        MoveImport("sui", "event"),
        MoveImport("std", "vector"),
        MoveImport("std", "bcs"),
        MoveImport("sui", "hash")
    )

    val module = MoveModule(
        name = moduleName,
        imports = imports,
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

// Common types
val UID = MoveType.Struct("sui::object", "UID")
val TxContext = MoveType.Struct("sui::tx_context", "TxContext")
val Clock = MoveType.Struct("sui::clock", "Clock")
fun Balance(t: MoveType) = MoveType.Struct("sui::balance", "Balance", listOf(t))
fun Coin(t: MoveType) = MoveType.Struct("sui::coin", "Coin", listOf(t))

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

private fun buildInstanceStruct(game: GameIR, dag: ActionDag): MoveStruct {
    val fields = buildList {
        add(MoveField("id", UID))

        // Roles
        game.roles.forEach { role ->
            add(MoveField(roleAddrName(role), MoveType.Address))
        }

        game.roles.forEach { role ->
            add(MoveField(roleJoinedName(role), MoveType.Bool))
        }

        add(MoveField("timeout_ms", MoveType.U64))
        add(MoveField("last_ts_ms", MoveType.U64))

        game.roles.forEach { role ->
            add(MoveField(roleBailedName(role), MoveType.Bool))
        }

        add(MoveField("pot", Balance(MoveType.TypeParam("Asset"))))

        add(MoveField("finalized", MoveType.Bool))

        game.roles.forEach { role ->
            add(MoveField(roleClaimAmountName(role), MoveType.U64))
            add(MoveField(roleClaimedName(role), MoveType.Bool))
        }

        // Game fields
        val visited = mutableSetOf<FieldRef>()
        dag.metas.forEach { meta ->
            meta.struct.visibility.forEach { (field, vis) ->
                if (!visited.add(field)) return@forEach

                val paramType = meta.spec.params.find { it.name == field.param }?.type ?: Type.IntType
                val moveType = translateType(paramType)

                // Clear value
                add(MoveField(fieldName(field.owner, field.param, false), moveType))
                add(MoveField(doneFlagName(field.owner, field.param, false), MoveType.Bool))

                // Commit value
                if (vis == Visibility.COMMIT) {
                    add(MoveField(fieldName(field.owner, field.param, true), MoveType.Vector(MoveType.U8)))
                    add(MoveField(doneFlagName(field.owner, field.param, true), MoveType.Bool))
                }
            }
        }

        // Action Done flags
        dag.topo().forEach { actionId ->
            add(MoveField("action_${actionId.first.name}_${actionId.second}_done", MoveType.Bool))
        }
    }

    return MoveStruct(
        name = instanceName(),
        abilities = listOf("key"),
        fields = fields,
        typeParams = listOf("phantom Asset")
    )
}

// ==========================================
// Function Building
// ==========================================

private fun buildInitFunction(): MoveFunction {
    return MoveFunction(
        name = "init",
        visibility = MoveVisibility.PRIVATE,
        params = listOf(MoveParam("ctx", MoveType.Ref(TxContext, true))),
        body = emptyList()
    )
}

private fun buildCreateGameFunction(game: GameIR, struct: MoveStruct): MoveFunction {
    val body = buildList {
        add(MoveStmt.Let("id", null, MoveExpr.Call("sui::object", "new", emptyList(), listOf(MoveExpr.Var("ctx")))))

        // Build instance
        val fields = struct.fields.map { field ->
            val value: MoveExpr = when(field.name) {
                "id" -> MoveExpr.Var("id")
                "timeout_ms" -> MoveExpr.Var("timeout_ms")
                "last_ts_ms" -> MoveExpr.U64Lit(0)
                "pot" -> MoveExpr.Call("sui::balance", "zero", listOf(MoveType.TypeParam("Asset")), emptyList())
                "finalized" -> MoveExpr.BoolLit(false)
                else -> {
                    if (field.type == MoveType.Bool) MoveExpr.BoolLit(false)
                    else if (field.type == MoveType.U64) MoveExpr.U64Lit(0)
                    else if (field.type == MoveType.Address) MoveExpr.AddressLit("0x0")
                    else if (field.type is MoveType.Vector) MoveExpr.Call("std::vector", "empty", listOf((field.type as MoveType.Vector).param), emptyList())
                    else error("Unknown field init for ${field.name}")
                }
            }
            MoveFieldInit(field.name, value)
        }

        add(MoveStmt.Let("instance", null, MoveExpr.StructInit(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), fields)))

        add(MoveStmt.ExprStmt(MoveExpr.Call("sui::transfer", "share_object", listOf(MoveType.TypeParam("Asset")), listOf(MoveExpr.Var("instance")))))
    }

    return MoveFunction(
        name = "create_game",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("timeout_ms", MoveType.U64),
            MoveParam("ctx", MoveType.Ref(TxContext, true))
        ),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildJoinFunction(role: RoleId, game: GameIR): MoveFunction {
    val body = buildList {
        val roleJoined = roleJoinedName(role)
        val roleAddr = roleAddrName(role)

        add(MoveStmt.Assert(
            MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleJoined)),
            100
        ))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleAddr),
            MoveExpr.Call("sui::tx_context", "sender", emptyList(), listOf(MoveExpr.Var("ctx")))
        ))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleJoined),
            MoveExpr.BoolLit(true)
        ))

        add(MoveStmt.ExprStmt(MoveExpr.Call(
            "sui::balance", "join", listOf(MoveType.TypeParam("Asset")),
            listOf(
                MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), true),
                MoveExpr.Call("sui::coin", "into_balance", listOf(MoveType.TypeParam("Asset")), listOf(MoveExpr.Var("payment")))
            )
        )))

        add(MoveStmt.Assign(
            MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
            MoveExpr.Call("sui::clock", "timestamp_ms", emptyList(), listOf(MoveExpr.Var("clock")))
        ))
    }

    return MoveFunction(
        name = "join_${role.name}",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)),
            MoveParam("payment", Coin(MoveType.TypeParam("Asset"))),
            MoveParam("clock", MoveType.Ref(Clock, false)),
            MoveParam("ctx", MoveType.Ref(TxContext, true))
        ),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildActionFunction(
    id: ActionId,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): MoveFunction {
    val meta = dag.meta(id)
    val idx = linearization.getValue(id)
    val struct = meta.struct
    val spec = meta.spec
    val kind = meta.kind
    val hidden = kind == Visibility.COMMIT

    val params = buildList {
        add(MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)))
        add(MoveParam("clock", MoveType.Ref(Clock, false)))
        add(MoveParam("ctx", MoveType.Ref(TxContext, true)))

        spec.params.forEach { p ->
            val type = if (hidden) MoveType.Vector(MoveType.U8) else translateType(p.type)
            val varName = inputParamName(p.name, hidden)
            add(MoveParam(varName, type))
        }

        if (kind == Visibility.REVEAL) {
            add(MoveParam("salt", MoveType.U64))
        }
    }

    val body = buildList {
        val owner = struct.owner
        add(MoveStmt.Assert(
            MoveExpr.BinOp(MoveBinOp.EQ,
                MoveExpr.Call("sui::tx_context", "sender", emptyList(), listOf(MoveExpr.Var("ctx"))),
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleAddrName(owner))
            ),
            101
        ))

        val now = MoveExpr.Call("sui::clock", "timestamp_ms", emptyList(), listOf(MoveExpr.Var("clock")))

        // Timeout check
        add(MoveStmt.If(
            MoveExpr.BinOp(MoveBinOp.GT, now, MoveExpr.BinOp(MoveBinOp.ADD,
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "last_ts_ms"),
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), "timeout_ms")
            )),
            listOf(
                MoveStmt.Assign(
                    MoveExpr.FieldAccess(MoveExpr.Var("instance"), roleBailedName(owner)),
                    MoveExpr.BoolLit(true)
                )
            )
        ))

        val actionDoneField = "action_${id.first.name}_${id.second}_done"
        add(MoveStmt.Assert(
            MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), actionDoneField)),
            102
        ))

        dag.prerequisitesOf(id).forEach { depId ->
            val depDoneField = "action_${depId.first.name}_${depId.second}_done"
            add(MoveStmt.Assert(
                MoveExpr.FieldAccess(MoveExpr.Var("instance"), depDoneField),
                103
            ))
        }

        if (!hidden) {
             val guards = translateDomainGuards(spec.params)
             guards.forEach { g ->
                 add(MoveStmt.Assert(g, 104))
             }

             if (spec.guardExpr != Expr.Const.BoolVal(true)) {
                 val guard = translateExpr(
                     spec.guardExpr,
                     contextOwner = owner,
                     contextParams = spec.params.map { it.name }.toSet()
                 )
                 add(MoveStmt.Assert(guard, 105))
             }
        }

        if (kind == Visibility.REVEAL) {
             spec.params.forEach { p ->
                 val input = MoveExpr.Var(inputParamName(p.name, false))
                 val salt = MoveExpr.Var("salt")

                 add(MoveStmt.Let("data_${p.name}", null, MoveExpr.Call("std::bcs", "to_bytes", listOf(translateType(p.type)), listOf(
                     MoveExpr.Borrow(input, false)
                 ))))
                 add(MoveStmt.ExprStmt(MoveExpr.Call("std::vector", "append", listOf(MoveType.U8), listOf(
                     MoveExpr.Borrow(MoveExpr.Var("data_${p.name}"), true),
                     MoveExpr.Call("std::bcs", "to_bytes", listOf(MoveType.U64), listOf(
                         MoveExpr.Borrow(salt, false)
                     ))
                 ))))

                 val hash = MoveExpr.Call("sui::hash", "keccak256", emptyList(), listOf(
                     MoveExpr.Borrow(MoveExpr.Var("data_${p.name}"), false)
                 ))

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

private fun buildFinalizeFunction(game: GameIR, dag: ActionDag): MoveFunction {
    val body = buildList {
        dag.sinks().forEach { sinkId ->
            val doneField = "action_${sinkId.first.name}_${sinkId.second}_done"
            add(MoveStmt.Assert(MoveExpr.FieldAccess(MoveExpr.Var("instance"), doneField), 107))
        }

        add(MoveStmt.Assert(MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), "finalized")), 108))

        add(MoveStmt.Let("total_payout", MoveType.U64, MoveExpr.U64Lit(0)))

        game.payoffs.forEach { (role, expr) ->
            val payoutExpr = translateExpr(expr, null, emptySet())
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
                MoveExpr.Call("sui::balance", "value", listOf(MoveType.TypeParam("Asset")), listOf(MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), false)))
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
             MoveParam("clock", MoveType.Ref(Clock, false)),
             MoveParam("ctx", MoveType.Ref(TxContext, true))
        ),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun buildClaimFunction(role: RoleId, game: GameIR): MoveFunction {
    val body = buildList {
        add(MoveStmt.Assert(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "finalized"), 110))

        val claimedField = roleClaimedName(role)
        add(MoveStmt.Assert(MoveExpr.UnaryOp(MoveUnaryOp.NOT, MoveExpr.FieldAccess(MoveExpr.Var("instance"), claimedField)), 111))

        add(MoveStmt.Assign(MoveExpr.FieldAccess(MoveExpr.Var("instance"), claimedField), MoveExpr.BoolLit(true)))

        val amountField = roleClaimAmountName(role)
        add(MoveStmt.Let("amount", MoveType.U64, MoveExpr.FieldAccess(MoveExpr.Var("instance"), amountField)))

        add(MoveStmt.If(
            MoveExpr.BinOp(MoveBinOp.GT, MoveExpr.Var("amount"), MoveExpr.U64Lit(0)),
            listOf(
                MoveStmt.Let("payout_coin", null, MoveExpr.Call("sui::coin", "take", listOf(MoveType.TypeParam("Asset")), listOf(
                    MoveExpr.Borrow(MoveExpr.FieldAccess(MoveExpr.Var("instance"), "pot"), true),
                    MoveExpr.Var("amount"),
                    MoveExpr.Var("ctx")
                ))),
                MoveStmt.ExprStmt(MoveExpr.Call("sui::transfer", "public_transfer", listOf(MoveType.TypeParam("Asset")), listOf(
                    MoveExpr.Var("payout_coin"),
                    MoveExpr.Call("sui::tx_context", "sender", emptyList(), listOf(MoveExpr.Var("ctx")))
                )))
            )
        ))
    }

    return MoveFunction(
        name = "claim_${role.name}",
        visibility = MoveVisibility.PUBLIC_ENTRY,
        params = listOf(
            MoveParam("instance", MoveType.Ref(MoveType.Struct(null, instanceName(), listOf(MoveType.TypeParam("Asset"))), true)),
            MoveParam("clock", MoveType.Ref(Clock, false)),
            MoveParam("ctx", MoveType.Ref(TxContext, true))
        ),
        body = body,
        typeParams = listOf("Asset")
    )
}

private fun translateType(t: Type): MoveType = when(t) {
    is Type.IntType -> MoveType.U64
    is Type.BoolType -> MoveType.Bool
    is Type.SetType -> MoveType.U64
}

private fun translateDomainGuards(params: List<ActionParam>): List<MoveExpr> =
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
    contextParams: Set<VarId>
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

    is Expr.Add -> MoveExpr.BinOp(MoveBinOp.ADD, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Sub -> MoveExpr.BinOp(MoveBinOp.SUB, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Mul -> MoveExpr.BinOp(MoveBinOp.MUL, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Div -> MoveExpr.BinOp(MoveBinOp.DIV, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Mod -> MoveExpr.BinOp(MoveBinOp.MOD, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))

    is Expr.Neg -> MoveExpr.UnaryOp(MoveUnaryOp.NEG, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Eq -> MoveExpr.BinOp(MoveBinOp.EQ, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Ne -> MoveExpr.BinOp(MoveBinOp.NEQ, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Lt -> MoveExpr.BinOp(MoveBinOp.LT, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Le -> MoveExpr.BinOp(MoveBinOp.LTE, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Gt -> MoveExpr.BinOp(MoveBinOp.GT, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Ge -> MoveExpr.BinOp(MoveBinOp.GTE, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))

    is Expr.And -> MoveExpr.BinOp(MoveBinOp.AND, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Or -> MoveExpr.BinOp(MoveBinOp.OR, translateExpr(expr.l, contextOwner, contextParams), translateExpr(expr.r, contextOwner, contextParams))
    is Expr.Not -> MoveExpr.UnaryOp(MoveUnaryOp.NOT, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Ite -> MoveExpr.IfElse(
        translateExpr(expr.c, contextOwner, contextParams),
        translateExpr(expr.t, contextOwner, contextParams),
        translateExpr(expr.e, contextOwner, contextParams)
    )
}

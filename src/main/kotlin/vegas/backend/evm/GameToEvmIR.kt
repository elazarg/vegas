package vegas.backend.evm

import vegas.RoleId
import vegas.FieldRef
import vegas.VarId
import vegas.ir.*
import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Main entry point: Compiles a GameIR into a generic EVM Contract Model.
 * Assumes the ActionDag has already been transformed (e.g. Commit-Reveal expansion).
 */
fun compileToEvm(game: GameIR): EvmContract {
    val dag = game.dag
    // 1. Linearize the DAG to get stable integer IDs for every action
    val linearization = linearizeDag(dag)

    // 2. Build the Storage Layout (State)
    val storage = buildStorage(game, dag, linearization)

    // 3. Build the Actions (Transitions)
    val actions = dag.topo().map { actionId ->
        buildAction(actionId, dag, linearization)
    }

    // 4. Build the Payoff Logic (Outcome)
    val payoffs = buildPayoffs(game)

    // 5. Build Initialization (Constructor)
    val init = listOf(
        Assign(
            Member(BuiltIn.Self, "lastTs"),
            BuiltIn.Timestamp
        )
    )

    return EvmContract(
        name = game.name,
        roles = game.roles.toList(),
        storage = storage,
        enums = listOf(buildRoleEnum(game)),
        events = emptyList(),
        actions = actions,
        payoffs = payoffs,
        initialization = init,
    )
}

// =========================================================================
// 1. Linearization & Naming
// =========================================================================

private fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.topo()
        .sortedWith(compareBy<ActionId> { it.second }.thenBy { it.first.name })
        .mapIndexed { idx, id -> id to idx }
        .toMap()


// =========================================================================
// 2. Storage Generation
// =========================================================================

// Naming Conventions for Storage
internal const val roleMap = "roles"
internal const val balanceMap = "balanceOf"
internal const val roleEnumName = "Role"
internal const val roleNone = "None"

internal fun roleAddr(role: String) = "address_$role"
internal fun roleJoined(role: String) = "done_$role"

private fun storageName(role: RoleId, param: VarId, hidden: Boolean): String =
    if (hidden) "${role.name}_${param}_hidden"
    else "${role.name}_${param}"

private fun doneFlagName(role: RoleId, param: VarId, hidden: Boolean): String {
    return "done_${storageName(role, param, hidden)}"
}

fun inputParam(param: VarId, hidden: Boolean): String {
    val prefix = if (hidden) "hidden_" else ""
    return "$prefix${param.name}"
}

private fun buildStorage(
    g: GameIR,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): List<EvmStorageSlot> = buildList {

    // Infrastructure
    add(EvmStorageSlot("lastTs", Uint256))
    add(EvmStorageSlot("actionDone", Mapping(EnumType(roleEnumName), Mapping(Uint256, Bool))))
    add(EvmStorageSlot("actionTimestamp", Mapping(EnumType(roleEnumName), Mapping(Uint256, Uint256))))

    // Action Constants
    linearization.forEach { (id, idx) ->
        val constName = "ACTION_${id.first.name}_${id.second}"
        add(EvmStorageSlot(constName, Uint256, IntLit(idx), isImmutable = true))
    }

    // FINAL_ACTION Constant
    val revealIds = dag.metas.filter { it.kind == Visibility.REVEAL }.map { it.id }
    val finalActionIdx = if (revealIds.isNotEmpty()) {
        revealIds.maxOf { linearization.getValue(it) }
    } else {
        linearization.values.maxOrNull() ?: 0
    }
    add(EvmStorageSlot("FINAL_ACTION", Uint256, IntLit(finalActionIdx), isImmutable = true))

    // Roles & Balances
    val roleType = EnumType(roleEnumName)
    add(EvmStorageSlot(roleMap, Mapping(Address, roleType)))
    add(EvmStorageSlot(balanceMap, Mapping(Address, Int256)))

    // Player State
    (g.roles + g.chanceRoles).forEach { role ->
        add(EvmStorageSlot(roleAddr(role.name), Address))
    }
    (g.roles + g.chanceRoles).forEach { role ->
        add(EvmStorageSlot(roleJoined(role.name), Bool)) // done_Role
    }
    add(EvmStorageSlot("payoffs_distributed", Bool))

    // Game Variables
    val visited = mutableSetOf<FieldRef>()
    dag.metas.forEach { meta ->
        meta.struct.visibility.forEach { (field, vis) ->
            if (!visited.add(field)) return@forEach

            // (Clear values)
            val paramType = meta.spec.params.find { it.name == field.param }?.type ?: Type.IntType
            val evmType = translateType(paramType)
            add(EvmStorageSlot(storageName(field.owner, field.param, false), evmType))
            add(EvmStorageSlot(doneFlagName(field.owner, field.param, false), Bool))

            // Commit (Hidden values)
            if (vis == Visibility.COMMIT) {
                // GM doesn't show hidden fields, assuming standard pattern
                add(EvmStorageSlot(storageName(field.owner, field.param, true), Bytes32))
                add(EvmStorageSlot(doneFlagName(field.owner, field.param, true), Bool))
            }
        }
    }
}

private fun buildRoleEnum(g: GameIR): EvmEnum {
    val values = listOf(roleNone) + (g.roles + g.chanceRoles).map { it.name }
    return EvmEnum(roleEnumName, values)
}

// =========================================================================
// 3. Action Generation
// =========================================================================

private fun buildAction(
    id: ActionId,
    dag: ActionDag,
    linearization: Map<ActionId, Int>
): EvmAction {
    val meta = dag.meta(id)
    val idx = linearization.getValue(id)
    val spec = meta.spec
    val kind = meta.kind // PUBLIC, COMMIT, or REVEAL
    val hidden = kind == Visibility.COMMIT

    // 3a. Inputs
    val inputs = buildList {
        // Standard params
        spec.params.forEach { p ->
            val type = if (hidden) Bytes32 else translateType(p.type)
            val varName = VarId(inputParam(p.name, hidden))
            add(EvmParam(varName, type))
        }
        // Reveals need a salt
        if (kind == Visibility.REVEAL) {
            add(EvmParam(VarId("salt"), Uint256))
        }
    }

    // 3c. Guards - `where` expressions
    val guards = if (!hidden) {
        translateDomainGuards(spec.params) + if (spec.guardExpr != Expr.Const.BoolVal(true)) {
            listOf(
                translateExpr(
                    spec.guardExpr,
                    contextOwner = meta.struct.owner,
                    contextParams = spec.params.map { it.name }.toSet()
                )
            )
        } else {
            listOf()
        }
    } else {
        listOf()
    }
    // 3c. Body Logic
    val body = buildList {
        // Join Logic (Deposit, Role assignment)
        if (spec.join != null) {
            val role = meta.struct.owner
            val deposit = spec.join.deposit.v

            // require(!joined_Role)
            add(
                Require(
                    Unary(UnaryOp.NOT, Member(BuiltIn.Self, "done_${role.name}")),
                    "already joined"
                )
            )

            // Handle Deposit
            if (deposit > 0) {
                add(
                    Require(
                        Binary(BinaryOp.EQ, BuiltIn.MsgValue, IntLit(deposit)),
                        "bad stake"
                    )
                )
                add(
                    Assign(
                        Index(Member(BuiltIn.Self, balanceMap), BuiltIn.MsgSender),
                        BuiltIn.MsgValue
                    )
                )
            }

            // Effects
            add(
                Assign(
                    Index(Member(BuiltIn.Self, roleMap), BuiltIn.MsgSender),
                    EnumValue(roleEnumName, role.name)
                )
            )
            add(Assign(Member(BuiltIn.Self, "address_${role.name}"), BuiltIn.MsgSender))
            add(Assign(Member(BuiltIn.Self, "done_${role.name}"), BoolLit(true)))
        }

        // Reveal Verification
        if (kind == Visibility.REVEAL) {
            spec.params.forEach { p ->
                // hash(param, salt) == stored_commitment
                val input = VarId(inputParam( p.name, false))
                val salt = VarId(inputParam( VarId("salt"), false))
                val packed = AbiEncode(listOf(Var(input), Var(salt)), isPacked = true) // Solidity style packing
                val hash = Keccak256(packed)

                val commitment = Member(BuiltIn.Self, storageName(meta.struct.owner, p.name, true))

                add(
                    Require(
                        Binary(BinaryOp.EQ, hash, commitment),
                        "reveal failed for ${p.name}"
                    )
                )
            }
        }

        // State Updates (Writing to Storage)
        spec.params.forEach { p ->
            val targetName = storageName(meta.struct.owner, p.name, hidden)
            val flagName = doneFlagName(meta.struct.owner, p.name, hidden)
            val varName = VarId(inputParam(p.name, hidden))

            add(Assign(Member(BuiltIn.Self, targetName), Var(varName)))
            add(Assign(Member(BuiltIn.Self, flagName), BoolLit(true)))
        }
    }

    // 3c. Dependencies & Metadata
    val dependencies = dag.prerequisitesOf(id).sortedBy { linearization.getValue(it) }
    // Simplistic check for terminality: if it's the last index, or explicitly marked in GameIR?
    // For now, we assume the backend calculates FINAL_ACTION based on max index.
    val isTerminal = false // The backend calculates this based on DAG topology usually
    val owner = if (spec.join != null) roleNone else meta.struct.owner.name
    return EvmAction(
        actionId = id,
        name = "move_${meta.struct.owner}_$idx",
        invokedBy = RoleId(owner),
        inputs = inputs,
        payable = (spec.join?.deposit?.v ?: 0) > 0,
        dependencies = dependencies,
        isTerminal = isTerminal,
        guards = guards,
        body = body
    )
}

// =========================================================================
// 4. Expression Translation
// =========================================================================

private fun buildPayoffs(game: GameIR): Map<String, EvmExpr> {
    return game.payoffs.mapKeys { it.key.name }.mapValues { (_, expr) ->
        translateExpr(expr, contextOwner = null, contextParams = emptySet())
    }
}

/** Generates 'require' statements for domain validation (e.g., `x in {1, 2, 3}`) */
private fun translateDomainGuards(params: List<ActionParam>): List<EvmExpr> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = Var(VarId(inputParam(p.name, false)))
                    t.values.map { Binary(BinaryOp.EQ, x, IntLit(it)) }.reduce<EvmExpr, EvmExpr> {
                        a, b -> Binary(BinaryOp.OR, a, b)
                    }
                }
            }
            else -> null
        }
    }

private fun translateExpr(
    expr: Expr,
    contextOwner: RoleId?,
    contextParams: Set<VarId>
): EvmExpr = when (expr) {
    is Expr.Const.IntVal -> IntLit(expr.v)
    is Expr.Const.BoolVal -> BoolLit(expr.v)
    is Expr.Const.Hidden -> error("Hidden constants should be resolved before backend")
    is Expr.Const.Opaque -> error("Opaque constants not supported")
    is Expr.Const.Quit -> error("Quit not supported")

    is Expr.Field -> {
        val (role, name) = expr.field
        // If we are inside an action and the field matches a parameter, read from Input
        if (contextOwner == role && name in contextParams) {
            Var(name)
        } else {
            // Otherwise read from Storage (always the clear value)
            Member(BuiltIn.Self, storageName(role, name, false))
        }
    }

    is Expr.IsDefined -> {
        val (role, name) = expr.field
        Member(BuiltIn.Self, doneFlagName(role, name, false))
    }

    is Expr.Add -> Binary(
        BinaryOp.ADD,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Sub -> Binary(
        BinaryOp.SUB,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Mul -> Binary(
        BinaryOp.MUL,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Div -> Binary(
        BinaryOp.DIV,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Neg -> Unary(UnaryOp.NEG, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Eq -> Binary(
        BinaryOp.EQ,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Ne -> Binary(
        BinaryOp.NE,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Lt -> Binary(
        BinaryOp.LT,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Le -> Binary(
        BinaryOp.LE,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Gt -> Binary(
        BinaryOp.GT,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Ge -> Binary(
        BinaryOp.GE,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.And -> Binary(
        BinaryOp.AND,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Or -> Binary(
        BinaryOp.OR,
        translateExpr(expr.l, contextOwner, contextParams),
        translateExpr(expr.r, contextOwner, contextParams)
    )

    is Expr.Not -> Unary(UnaryOp.NOT, translateExpr(expr.x, contextOwner, contextParams))

    is Expr.Ite -> Ternary(
        translateExpr(expr.c, contextOwner, contextParams),
        translateExpr(expr.t, contextOwner, contextParams),
        translateExpr(expr.e, contextOwner, contextParams)
    )
}

private fun translateType(t: Type): EvmType = when (t) {
    is Type.IntType -> Int256 // Or Uint256 depending on preference
    is Type.BoolType -> Bool
    is Type.SetType -> Int256
}

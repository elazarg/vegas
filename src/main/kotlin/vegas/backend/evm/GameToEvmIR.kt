package vegas.backend.evm

import vegas.RoleId
import vegas.FieldRef
import vegas.VarId
import vegas.ir.*
import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*
import vegas.frontend.SAMPLE_OWNER
import vegas.semantics.payoutRanges
import java.math.BigInteger

/**
 * Terminal-audit policy for [compileToEvm].
 *
 * A player's first departure is collected with probability at least
 * [coverage], so a bond of `range / coverage` deters every departure whose
 * gain is at most `range` (VegasCore's `rosterAuditDeposit`). The range is the
 * role's payout range over every way the game can end ([payoutRanges]); for a
 * game too large to enumerate it is the whole pot, which bounds every payout.
 */
data class AuditPolicy(
    val coverage: vegas.Rational = vegas.Rational(1),
    val windowSeconds: Int = 7 * 86400,
) {
    init {
        require(coverage.numerator > 0 && coverage.numerator <= coverage.denominator) {
            "coverage must be in (0, 1], got $coverage"
        }
        require(windowSeconds > 0) { "audit window must be positive" }
    }

    /** The bond for a payout range: `ceil(range / coverage)`. */
    fun bond(range: Int): Int =
        ((range.toLong() * coverage.denominator + coverage.numerator - 1) / coverage.numerator).toInt()
}

/**
 * Main entry point: Compiles a GameIR into a generic EVM Contract Model.
 * Assumes the EventGraph has already been transformed (e.g. Commit-Reveal expansion).
 */
fun compileToEvm(game: GameIR, audit: AuditPolicy? = null): EvmContract {
    val dag = game.dag
    val evmAudit = audit?.let { policy ->
        val pot = game.roles.sumOf { dag.deposit(it).v }
        val ranges = payoutRanges(game)
        EvmAudit(
            bonds = game.payoffs.keys.associateWith { role -> policy.bond(ranges?.get(role)?.width ?: pot) },
            windowSeconds = policy.windowSeconds,
        )
    }
    // Private draws are the players' own knowledge and have no on-chain
    // presence: they leave the schedule, and a node that waited for one
    // waits for its predecessors instead.
    val order = scheduleOrder(dag).filterNot { dag.isPrivateDraw(it) }
    val position = order.withIndex().associate { (i, id) -> id to i }
    fun onChainPredecessors(id: NodeId): Set<NodeId> = dag.prerequisitesOf(id).flatMap { p ->
        if (dag.isPrivateDraw(p)) onChainPredecessors(p) else setOf(p)
    }.toSet()
    // An audited service grants events one at a time, in schedule order, as
    // VegasCore's roster service does: each event also waits for the event
    // granted before it. Joins stay concurrent; they precede play.
    val events = order.filter { dag.spec(it).join == null }
    val grantedBefore: Map<NodeId, NodeId> =
        if (audit == null) emptyMap() else events.zipWithNext().associate { (before, next) -> next to before }

    val schedule = EvmSchedule(
        nodes = order.map { id ->
            EvmScheduleNode(
                actionId = id,
                owner = dag.owner(id),
                predecessors = (onChainPredecessors(id) + listOfNotNull(grantedBefore[id]))
                    .map { position.getValue(it) }.distinct().sorted(),
                kind = when {
                    dag.spec(id).join != null -> EvmNodeKind.JOIN
                    isBeaconDraw(dag, id) -> EvmNodeKind.DRAW
                    else -> EvmNodeKind.MOVE
                },
                commitment = dag.kind(id) == Visibility.COMMIT,
            )
        },
        draws = order.filter { isBeaconDraw(dag, it) }.map { buildDraw(it, dag, position.getValue(it)) },
    )

    return EvmContract(
        name = game.name,
        roles = game.roles.toList(),
        storage = buildStorage(game, dag, order),
        enums = listOf(buildRoleEnum(game)),
        events = emptyList(),
        schedule = schedule,
        actions = order.filterNot { isBeaconDraw(dag, it) }.map { buildAction(it, dag, position.getValue(it), evmAudit) },
        withdrawals = buildWithdrawals(game),
        initialization = emptyList(),
        audit = evmAudit,
    )
}

// =========================================================================
// 1. Schedule order & Naming
// =========================================================================

/**
 * A deterministic topological order: among ready nodes, the one with the
 * least (step index, role name) goes first.
 */
private fun scheduleOrder(dag: EventGraph): List<NodeId> {
    val byKey = compareBy<NodeId> { it.second }.thenBy { it.first.name }
    val remaining = dag.actions.associateWith { dag.prerequisitesOf(it).size }.toMutableMap()
    val ready = java.util.PriorityQueue(byKey).apply { addAll(remaining.filterValues { it == 0 }.keys) }
    val order = mutableListOf<NodeId>()
    while (ready.isNotEmpty()) {
        val id = ready.poll()
        order += id
        for (d in dag.dependentsOf(id)) {
            val left = remaining.getValue(d) - 1
            remaining[d] = left
            if (left == 0) ready += d
        }
    }
    check(order.size == dag.actions.size) { "event graph is cyclic" }
    return order
}

private fun isBeaconDraw(dag: EventGraph, id: NodeId): Boolean =
    dag.sampleSpec(id)?.source == EntropySource.Beacon

// =========================================================================
// 2. Storage Generation
// =========================================================================

// Naming Conventions for Storage
internal const val roleMap = "roles"
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

internal fun actionConst(id: NodeId) = "ACTION_${id.first.name}_${id.second}"

private fun buildStorage(
    g: GameIR,
    dag: EventGraph,
    order: List<NodeId>,
): List<EvmStorageSlot> = buildList {

    // Schedule positions
    order.forEachIndexed { idx, id ->
        add(EvmStorageSlot(actionConst(id), Uint256, IntLit(idx), isImmutable = true))
    }

    // Roles & Balances
    val roleType = EnumType(roleEnumName)
    add(EvmStorageSlot(roleMap, Mapping(Address, roleType)))

    // Player State. SAMPLE_OWNER has no actor (no join, no payout); the
    // address / joined / claimed slots would be dead storage.
    val actorRoles = (g.roles + g.chanceRoles).filter { it != SAMPLE_OWNER }
    actorRoles.forEach { role ->
        add(EvmStorageSlot(roleAddr(role.name), Address))
    }
    actorRoles.forEach { role ->
        add(EvmStorageSlot(roleJoined(role.name), Bool)) // done_Role
    }

    // Per-role claimed flags
    actorRoles.forEach { role ->
        add(EvmStorageSlot("claimed_${role.name}", Bool))
    }

    // Game Variables, in schedule order
    val visited = mutableSetOf<FieldRef>()
    order.map { dag.meta(it) }.forEach { meta ->
        meta.struct.visibility.forEach { (field, vis) ->
            if (!visited.add(field)) return@forEach

            // (Clear values)
            val paramType = meta.spec.params.find { it.name == field.param }?.type ?: Type.IntType
            val evmType = translateType(paramType)
            add(EvmStorageSlot(storageName(field.owner, field.param, false), evmType))
            add(EvmStorageSlot(doneFlagName(field.owner, field.param, false), Bool))

            // Commit (Hidden values)
            if (vis == Visibility.COMMIT) {
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
    id: NodeId,
    dag: EventGraph,
    idx: Int,
    audit: EvmAudit?,
): EvmAction {
    val meta = dag.meta(id)
    val spec = meta.spec
    val kind = meta.kind // PUBLIC, COMMIT, or REVEAL
    val hidden = kind == Visibility.COMMIT

    val inputs = buildList {
        if (audit != null) add(EvmParam(CONTEXT_PARAM, Bytes32))
        spec.params.forEach { p ->
            val type = if (hidden) Bytes32 else translateType(p.type)
            add(EvmParam(VarId(inputParam(p.name, hidden)), type))
        }
        // Reveals need a salt
        if (kind == Visibility.REVEAL) {
            add(EvmParam(VarId("salt"), Uint256))
        }
    }

    // Guards - `where` expressions, checked when the value becomes public.
    val guards = if (!hidden) {
        translateDomainGuards(spec.params) +
            translateSampleSupportGuards(meta) +
            if (spec.guardExpr != Expr.Const.BoolVal(true)) {
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

    val body = buildList {
        // Join Logic (Deposit, Role assignment)
        if (spec.join != null) {
            val role = meta.struct.owner
            val deposit = spec.join.deposit.v + (audit?.bonds?.get(role) ?: 0)

            add(
                Require(
                    Unary(UnaryOp.NOT, Member(BuiltIn.Self, "done_${role.name}")),
                    "already joined"
                )
            )
            // A zero-deposit join is non-payable, which already rejects value.
            if (deposit > 0) {
                add(
                    Require(
                        Binary(BinaryOp.EQ, BuiltIn.MsgValue, IntLit(deposit)),
                        "bad stake"
                    )
                )
            }
            add(
                Assign(
                    Index(Member(BuiltIn.Self, roleMap), BuiltIn.MsgSender),
                    EnumValue(roleEnumName, role.name)
                )
            )
            add(Assign(Member(BuiltIn.Self, "address_${role.name}"), BuiltIn.MsgSender))
            add(Assign(Member(BuiltIn.Self, "done_${role.name}"), BoolLit(true)))
        }

        // Reveal Verification - uses role/actor-bound commitments to prevent copy-commit attacks
        if (kind == Visibility.REVEAL) {
            spec.params.forEach { p ->
                val input = Var(VarId(inputParam(p.name, false)))
                val salt = Var(VarId(inputParam(VarId("salt"), false)))
                val commitment = Member(BuiltIn.Self, storageName(meta.struct.owner, p.name, true))

                add(CheckReveal(commitment, meta.struct.owner, listOf(input, salt)))
            }
        }

        spec.params.forEach { p ->
            val targetName = storageName(meta.struct.owner, p.name, hidden)
            val flagName = doneFlagName(meta.struct.owner, p.name, hidden)
            val varName = VarId(inputParam(p.name, hidden))

            add(Assign(Member(BuiltIn.Self, targetName), Var(varName)))
            add(Assign(Member(BuiltIn.Self, flagName), BoolLit(true)))
        }
    }

    val join = spec.join
    return EvmAction(
        actionId = id,
        node = idx,
        name = "move_${meta.struct.owner}_$idx",
        invokedBy = if (join != null) RoleId(roleNone) else meta.struct.owner,
        inputs = inputs,
        payable = join != null && join.deposit.v + (audit?.bonds?.get(meta.struct.owner) ?: 0) > 0,
        isJoin = join != null,
        value = if (join == null) 0 else join.deposit.v + (audit?.bonds?.get(meta.struct.owner) ?: 0),
        guards = guards,
        body = body
    )
}

/**
 * The effect of a beacon draw. The beacon output is domain-separated by
 * contract and node, then mapped onto the declared distribution: with
 * weights `w_k / D` over a common denominator `D`, the value is `v_k` for
 * the `k` with `c_{k-1} <= r < c_k`, where `r = seed mod D` and `c` are the
 * cumulative integer weights. The bias of the reduction is below `D / 2^256`.
 */
private fun buildDraw(id: NodeId, dag: EventGraph, idx: Int): EvmDraw {
    val meta = dag.meta(id)
    val dist = meta.sample?.dist
        ?: error("EVM emission for sample requires an explicit distribution; got none for $id. Multi-parameter samples are not supported.")
    val p = meta.spec.params.singleOrNull()
        ?: error("EVM emission supports only single-parameter samples; got ${meta.spec.params.size} params on $id.")
    val denominator = dist.support.fold(BigInteger.ONE) { acc, (_, w) -> lcm(acc, w.denominator.toBigInteger().abs()) }
    val weights = dist.support.map { (_, w) ->
        w.numerator.toBigInteger().abs() * (denominator / w.denominator.toBigInteger().abs())
    }
    val cumulative = weights.runningReduce { a, b -> a + b }
    check(cumulative.last() == denominator) { "distribution on $id does not sum to one" }
    require(denominator.bitLength() < 31) { "distribution denominator on $id is too large" }

    val seed = AbiEncodeRaw(listOf(Var(BEACON_VALUE), BuiltIn.Self, Cast(Uint256, IntLit(idx))))
    val r = Var(VarId("r"))
    val targetType = translateType(p.type)
    // Integer literals are typed explicitly: Solidity would give a ternary of
    // small literals the type uint8, which does not convert to int256.
    val literals = dist.support.map { (v, _) ->
        literalOfConst(v).let { if (targetType == Int256) Cast(Int256, it) else it }
    }
    val picked = literals.indices.toList().dropLast(1).foldRight<Int, EvmExpr>(literals.last()) { k, acc ->
        Ternary(Binary(BinaryOp.LT, r, IntLit(cumulative[k].toInt())), literals[k], acc)
    }
    return EvmDraw(
        node = idx,
        body = listOf(
            VarDecl("_r", Uint256, Binary(BinaryOp.MOD, Cast(Uint256, Keccak256(seed)), IntLit(denominator.toInt()))),
            Assign(Member(BuiltIn.Self, storageName(meta.struct.owner, p.name, false)), picked),
            Assign(Member(BuiltIn.Self, doneFlagName(meta.struct.owner, p.name, false)), BoolLit(true)),
        ),
    )
}

private fun lcm(a: BigInteger, b: BigInteger): BigInteger = a / a.gcd(b) * b

private fun buildWithdrawals(game: GameIR): List<EvmWithdrawal> =
    game.payoffs.entries.map { (role, expr) ->
        EvmWithdrawal(
            role = role,
            name = "withdraw_${role.name}",
            payout = translateExpr(expr, contextOwner = null, contextParams = emptySet()),
            refund = game.dag.deposit(role).v,
        )
    }

/** Lift an IR Const literal into an EVM IR expression literal. */
private fun literalOfConst(c: Expr.Const): EvmExpr = when (c) {
    is Expr.Const.IntVal -> IntLit(c.v)
    is Expr.Const.BoolVal -> BoolLit(c.v)
    else -> error("Unsupported const in sample support: $c")
}

/** Generates 'require' statements for domain validation (e.g., `x in {0..2}`) */
private fun translateDomainGuards(params: List<NodeParam>): List<EvmExpr> =
    params.mapNotNull { p ->
        when (val t = p.type) {
            is Type.RangeType -> {
                val x = Var(VarId(inputParam(p.name, false)))
                Binary(BinaryOp.AND,
                    Binary(BinaryOp.GE, x, IntLit(t.min)),
                    Binary(BinaryOp.LE, x, IntLit(t.max)))
            }
            else -> null
        }
    }

/**
 * Generate 'require' statements that the submitted value lies in the
 * declared distribution's support. Single-parameter sample nodes with
 * an explicit Dist enforce this on-chain: without it, anyone calling
 * the sample function could submit a value outside the support of
 * `~ uniform/weighted { ... }` (the type range alone may be wider).
 *
 * This is a stopgap on the way to a real entropy-source taxonomy
 * (block.prevrandao / VRF / drand): until that lands, the on-chain
 * contract trusts the caller's submission, but at least pins the
 * value to the declared support so the analysis-time and on-chain
 * supports agree.
 */
private fun translateSampleSupportGuards(meta: NodeMeta): List<EvmExpr> {
    val dist = meta.sample?.dist ?: return emptyList()
    val param = meta.spec.params.singleOrNull() ?: return emptyList()
    val x = Var(VarId(inputParam(param.name, false)))
    val supportLits: List<EvmExpr> = dist.support.mapNotNull { (v, _) ->
        when (v) {
            is Expr.Const.IntVal -> IntLit(v.v)
            is Expr.Const.BoolVal -> BoolLit(v.v)
            else -> null
        }
    }
    if (supportLits.isEmpty()) return emptyList()
    val disjunction = supportLits
        .map { Binary(BinaryOp.EQ, x, it) }
        .reduce { a, b -> Binary(BinaryOp.OR, a, b) }
    return listOf(disjunction)
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

    is Expr.Mod -> Binary(
        BinaryOp.MOD,
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
    is Type.RangeType -> Int256
}

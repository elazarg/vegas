package vegas.backend.gambit

import vegas.FieldRef
import vegas.Rational
import vegas.RoleId
import vegas.StaticError
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.ActionDag
import vegas.ir.ActionGameIR
import vegas.ir.ActionId
import vegas.ir.ActionStruct
import vegas.ir.Expr
import vegas.ir.Type
import vegas.ir.Visibility
import vegas.ir.dag

/**
 * Build a Gambit EFG string from the ActionDag-based IR.
 */
fun generateExtensiveFormGame(ir: ActionGameIR): String {
    val builder = DagGameTreeBuilder(ir)
    val tree = builder.build()
    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from ActionDag",
        strategicPlayers = ir.roles,
        tree = tree
    ).toEfg()
}

private data class ProducedValue(val source: ActionId, val value: IrVal)
private typealias State = Map<FieldRef, ProducedValue>

private class DagGameTreeBuilder(private val ir: ActionGameIR) {
    private val dag: ActionDag = ir.dag
    private val infosets = InfosetManager(ir.roles)
    private val chancePlayers: Set<RoleId> = ir.chanceRoles

    fun build(): GameTree {
        val frontier = FrontierMachine.from(dag)
        return buildFromFrontier(frontier, emptyMap())
    }

    private fun buildFromFrontier(frontier: FrontierMachine<ActionId>, state: State): GameTree {
        if (frontier.isComplete()) return terminalFrom(state)

        val enabled = frontier.enabled()
        require(enabled.isNotEmpty()) { "Frontier has no enabled actions but is not complete" }

        val actionsByRole: Map<RoleId, List<ActionId>> = enabled.groupBy { dag.owner(it) }
        val roles: List<RoleId> = actionsByRole.keys.sortedBy { it.name }

        // Pre-compute available choices for each role using the same pre-move state so
        // incomparable actions remain simultaneous (no information leakage between them).
        val roleChoices: Map<RoleId, List<Map<ActionId, Map<VarId, IrVal>>>> = roles.associateWith { role ->
            enumerateRoleChoices(actionsByRole.getValue(role), state)
        }

        if (roleChoices.values.any { it.isEmpty() }) {
            return terminalFrom(state)
        }

        fun advance(selections: Map<ActionId, Map<VarId, IrVal>>): GameTree {
            val nextFrontier = frontier.copy()
            var nextState = state
            selections.forEach { (actionId, packet) ->
                val struct = dag.struct(actionId)
                nextState = applyMove(actionId, struct, nextState, packet)
                nextFrontier.resolve(actionId)
            }
            return buildFromFrontier(nextFrontier, nextState)
        }

        fun buildRoleDecision(idx: Int, selections: Map<ActionId, Map<VarId, IrVal>>): GameTree {
            if (idx == roles.size) return advance(selections)

            val role = roles[idx]
            val actions = actionsByRole.getValue(role)
            val infosetKey = infosetView(role, actions, state)
            val infosetId = infosets.getInfosetNumber(role, infosetKey)
            val isChance = role in chancePlayers

            val choicesForRole = roleChoices.getValue(role)
            val probability = if (isChance) Rational(1, choicesForRole.size) else null

            val choices = choicesForRole.map { selection ->
                val mergedSelections = selections + selection
                val flattenedAction = selection.values.flatMap { it.entries }.associate { it.toPair() }
                GameTree.Choice(
                    action = flattenedAction,
                    probability = probability,
                    subtree = buildRoleDecision(idx + 1, mergedSelections),
                )
            }

            if (!isChance && choices.size == 1 && actions.all { dag.params(it).isEmpty() }) {
                return choices.first().subtree
            }

            return GameTree.Decision(
                owner = role,
                infosetId = infosetId,
                choices = choices,
                isChance = isChance,
            )
        }

        return buildRoleDecision(0, emptyMap())
    }

    private fun enumerateRoleChoices(
        actions: List<ActionId>,
        state: State,
    ): List<Map<ActionId, Map<VarId, IrVal>>> {
        val perAction: List<Pair<ActionId, List<Map<VarId, IrVal>>>> = actions.map { actionId ->
            val struct = dag.struct(actionId)
            val spec = dag.spec(actionId)
            val packets = enumeratePackets(actionId, struct, spec, state)
                .filter { pkt -> guardHolds(actionId, struct, spec, state, pkt) }
            actionId to packets
        }

        return cartesian(perAction.map { it.second }).map { combination ->
            perAction.mapIndexed { idx, (actionId, _) -> actionId to combination[idx] }.toMap()
        }
    }

    private fun terminalFrom(state: State): GameTree.Terminal {
        val pay = ir.payoffs.mapValues { (_, e) -> evalExpr(stateValues(state), e).toOutcome() }
        return GameTree.Terminal(pay)
    }

    private fun stateValues(state: State): Map<FieldRef, IrVal> = state.mapValues { (_, v) -> v.value }

    private fun infosetView(role: RoleId, actions: List<ActionId>, state: State): Map<FieldRef, IrVal> {
        val merged = mutableMapOf<FieldRef, IrVal>()
        actions.sortedBy { it.second }.forEach { actionId ->
            val view = stateView(actionId, role, state)
            view.forEach { (field, value) ->
                if (field !in merged || merged[field] == IrVal.Undefined) {
                    merged[field] = value
                }
            }
        }
        return merged
    }

    private fun stateView(target: ActionId, observer: RoleId, state: State): Map<FieldRef, IrVal> {
        val view = mutableMapOf<FieldRef, IrVal>()
        for ((field, produced) in state) {
            if (!dag.reaches(produced.source, target)) continue
            val vis = dag.visibilityOf(produced.source)[field] ?: continue
            val visibleValue = when (vis) {
                Visibility.PUBLIC, Visibility.REVEAL -> produced.value.unwrap()
                Visibility.COMMIT -> if (field.role == observer) produced.value.unwrap() else IrVal.Undefined
            }
            view[field] = visibleValue
        }
        return view
    }

    private fun enumeratePackets(
        actionId: ActionId,
        struct: ActionStruct,
        spec: vegas.ir.ActionSpec,
        state: State,
    ): List<Map<VarId, IrVal>> {
        if (spec.params.isEmpty()) return listOf(emptyMap())

        val role = struct.role
        val view = stateView(actionId, role, state)

        val choicesPerParam: List<List<Pair<VarId, IrVal>>> = spec.params.map { param ->
            val field = FieldRef(role, param.name)
            val vis = struct.visibility.getValue(field)
            val current = view[field]
            val options = when (vis) {
                Visibility.REVEAL -> if (current != null && current != IrVal.Undefined) listOf(current.unwrap()) else emptyList()
                Visibility.PUBLIC, Visibility.COMMIT -> enumerateType(param.type)
            }
            options.map { value -> param.name to value }
        }

        return cartesian(choicesPerParam).map { it.toMap() }
    }

    private fun guardHolds(
        actionId: ActionId,
        struct: ActionStruct,
        spec: vegas.ir.ActionSpec,
        state: State,
        packet: Map<VarId, IrVal>,
    ): Boolean {
        val role = struct.role
        val baseView = stateView(actionId, role, state).toMutableMap()
        packet.forEach { (name, value) ->
            baseView[FieldRef(role, name)] = value
        }
        return evalExpr(baseView, spec.guardExpr).asBool()
    }

    private fun applyMove(
        actionId: ActionId,
        struct: ActionStruct,
        state: State,
        packet: Map<VarId, IrVal>,
    ): State {
        val role = struct.role
        val updated = state.toMutableMap()
        packet.forEach { (name, value) ->
            val field = FieldRef(role, name)
            val vis = struct.visibility.getValue(field)
            val stored = when (vis) {
                Visibility.COMMIT -> IrVal.Hidden(value)
                Visibility.REVEAL, Visibility.PUBLIC -> value
            }
            updated[field] = ProducedValue(actionId, stored)
        }
        return updated
    }

    private fun enumerateType(type: Type): List<IrVal> = when (type) {
        is Type.BoolType -> listOf(IrVal.BoolVal(true), IrVal.BoolVal(false))
        is Type.SetType -> type.values.sorted().map { v -> IrVal.IntVal(v) }
        is Type.IntType -> throw StaticError("Cannot enumerate IntType; use SetType or BoolType")
    }

    private fun <T> cartesian(lists: List<List<T>>): List<List<T>> =
        lists.fold(listOf(emptyList())) { acc, xs -> acc.flatMap { a -> xs.map { a + it } } }
}

private fun IrVal.unwrap(): IrVal = when (this) {
    is IrVal.Hidden -> inner
    else -> this
}

// -----------------------------
// Minimal IR evaluator with visibility rules
// -----------------------------

/** Runtime values for IR expressions. */
internal sealed class IrVal {
    data class IntVal(val v: Int) : IrVal()
    data class BoolVal(val v: Boolean) : IrVal()
    data class Hidden(val inner: IrVal) : IrVal()   // value chosen but not visible to others
    object Undefined : IrVal()

    fun toOutcome(): IntVal = when (this) {
        is IntVal -> IntVal(v)
        is BoolVal -> IntVal(if (v) 1 else 0)
        is Hidden, Undefined -> error("Terminal payoff references undefined/hidden value")
    }

    fun asBool(): Boolean = when (this) {
        is BoolVal -> v
        is IntVal -> v != 0
        is Hidden, Undefined -> false
    }

    fun asInt(): Int = when (this) {
        is IntVal -> v
        is BoolVal -> if (v) 1 else 0
        is Hidden, Undefined -> error("Expected int, got $this")
    }
}

private fun evalExpr(env: Map<FieldRef, IrVal>, e: Expr): IrVal {
    fun get(field: FieldRef): IrVal = env[field] ?: IrVal.Undefined

    fun eq(a: IrVal, b: IrVal): Boolean = when {
        a is IrVal.IntVal && b is IrVal.IntVal -> a.v == b.v
        a is IrVal.BoolVal && b is IrVal.BoolVal -> a.v == b.v
        a is IrVal.Undefined && b is IrVal.Undefined -> true
        else -> false
    }

    fun eval(x: Expr): IrVal = when (x) {
        is Expr.IntVal -> IrVal.IntVal(x.v)
        is Expr.BoolVal -> IrVal.BoolVal(x.v)
        is Expr.Field -> get(x.field)
        is Expr.IsDefined -> {
            val v = get(x.field)
            IrVal.BoolVal(v !is IrVal.Undefined && v !is IrVal.Hidden)
        }

        is Expr.Add -> IrVal.IntVal(eval(x.l).asInt() + eval(x.r).asInt())
        is Expr.Sub -> IrVal.IntVal(eval(x.l).asInt() - eval(x.r).asInt())
        is Expr.Mul -> IrVal.IntVal(eval(x.l).asInt() * eval(x.r).asInt())
        is Expr.Div -> IrVal.IntVal(eval(x.l).asInt() / eval(x.r).asInt())
        is Expr.Neg -> IrVal.IntVal(-eval(x.x).asInt())

        is Expr.Eq -> IrVal.BoolVal(eq(eval(x.l), eval(x.r)))
        is Expr.Ne -> IrVal.BoolVal(!eq(eval(x.l), eval(x.r)))
        is Expr.Lt -> IrVal.BoolVal(eval(x.l).asInt() < eval(x.r).asInt())
        is Expr.Le -> IrVal.BoolVal(eval(x.l).asInt() <= eval(x.r).asInt())
        is Expr.Gt -> IrVal.BoolVal(eval(x.l).asInt() > eval(x.r).asInt())
        is Expr.Ge -> IrVal.BoolVal(eval(x.l).asInt() >= eval(x.r).asInt())

        is Expr.And -> IrVal.BoolVal(eval(x.l).asBool() && eval(x.r).asBool())
        is Expr.Or -> IrVal.BoolVal(eval(x.l).asBool() || eval(x.r).asBool())
        is Expr.Not -> IrVal.BoolVal(!eval(x.x).asBool())
        is Expr.Ite -> if (eval(x.c).asBool()) eval(x.t) else eval(x.e)
    }

    return eval(e)
}

/**
 * Manages information set identification and numbering.
 */
private class InfosetManager(roles: Set<RoleId>) {
    private val counters = roles.associateWith<RoleId, MutableMap<Map<FieldRef, IrVal>, Int>> { mutableMapOf() }
    private var chanceCounter: Int = 0

    fun getInfosetNumber(role: RoleId, key: Map<FieldRef, IrVal>): Int {
        if (role !in counters) {
            chanceCounter += 1
            return chanceCounter
        }
        val map = counters.getValue(role)
        return map.getOrPut(key) { map.size }
    }
}


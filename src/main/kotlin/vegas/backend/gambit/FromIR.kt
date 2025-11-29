package vegas.backend.gambit

import vegas.FieldRef
import vegas.Rational
import vegas.RoleId
import vegas.StaticError
import vegas.VarId
import vegas.dag.FrontierMachine
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.ActionSpec
import vegas.ir.ActionStruct
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.Visibility

/**
 * Build a Gambit EFG string from the ActionDag-based IR.
 *
 * Semantics (informally):
 *
 *  - The ActionDag is a partial order of actions. At runtime, we explore it by
 *    repeatedly taking a *frontier* of currently enabled actions. Each resolved
 *    frontier contributes one "epistemic layer" of writes along a history.
 *
 *  - Global state is represented as a stack of frontier slices:
 *      each slice is a map from (role, variable) to the IrVal written by some
 *      action in that frontier.  The stack order is the order in which frontiers
 *      are resolved along that history.
 *
 *  - Each player maintains a parallel stack of *redacted* slices (a KnowledgeMap):
 *      * their own fields are seen with their actual values;
 *      * other players' committed (hidden) values appear as Quit;
 *      * Quit is used for abandonment ("bail") and is never hidden.
 *
 *  - An information set for a role is keyed purely by that role's redacted stack.
 *    This yields perfect recall in the usual extensive-form sense: the role can
 *    always recover what it has previously done and observed.
 *
 *  - Each resolved frontier is treated as a simultaneous-move round:
 *      * all actions enabled in that frontier execute exactly once per history;
 *      * for each role we enumerate joint packets for all of its actions in that
 *        frontier (subject to guards);
 *      * after all roles choose, the resulting frontier slice is pushed onto the
 *        global state and all players’ knowledge stacks.
 *
 * This layering is epistemic, not part of the IR itself: it is induced by the
 * frontier exploration of the ActionDag and respects its causal partial order.
 */
fun generateExtensiveFormGame(ir: GameIR): String {
    val builder = DagGameTreeBuilder(ir)
    val tree = builder.build()
    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from ActionDag",
        strategicPlayers = ir.roles,
        tree = tree
    ).toEfg()
}

private typealias FrontierSlice = Map<FieldRef, IrVal>

/**
 * Visible snapshot to 'who' at a given frontier: others' Hidden appear as Opaque.
 * Bail/abandonment is represented by IrVal.Quit and is never hidden.
 */
private fun redacted(messages: FrontierSlice, who: RoleId): FrontierSlice =
    messages.mapValues { (fieldRef, v) ->
        val (r, _) = fieldRef
        if (r == who) {
            if (v is IrVal.Hidden) v.inner else v
        } else when (v) {
            is IrVal.Hidden -> IrVal.Opaque  // Others see that commitment happened, not the value
            else -> v  // Quit (bail) and other values pass through
        }
    }

/**
 * A stack of frontier maps. This plays a dual role:
 *  - as the global heap of concrete writes (State),
 *  - as each player's redacted knowledge state.
 */
private data class Infoset(
    val lastFrontier: FrontierSlice = emptyMap(),
    val past: Infoset? = null,
) {
    fun get(f: FieldRef): IrVal =
        lastFrontier[f] ?: (past?.get(f) ?: IrVal.Quit)

    infix fun with(newFrontier: FrontierSlice): Infoset =
        Infoset(newFrontier, this)
}

private typealias State = Infoset
private typealias KnowledgeMap = Map<RoleId, Infoset>

/** Has this role ever written Quit (i.e., bailed) along this history? */
private fun Infoset.quit(role: RoleId): Boolean =
    lastFrontier.any { (field, v) -> field.role == role && v == IrVal.Quit } ||
            (past?.quit(role) ?: false)

/** Helper to build a FrontierSlice from role + packet over variables. */
private fun toFrontierMap(role: RoleId, pkt: Map<VarId, IrVal>): FrontierSlice =
    pkt.mapKeys { (v, _) -> FieldRef(role, v) }

/**
 * Manages information set identification and numbering.
 * Key: the full redacted history (Infoset stack) of that role.
 */
private class InfosetManager(roles: Set<RoleId>) {
    private val perRole: Map<RoleId, MutableMap<Infoset, Int>> =
        roles.associateWith { mutableMapOf() }

    private var chanceCounter: Int = 0

    fun getInfosetNumber(role: RoleId, key: Infoset): Int {
        if (role !in perRole) {
            chanceCounter += 1
            return chanceCounter
        }
        val table = perRole.getValue(role)
        return table.getOrPut(key) { table.size } // 0-based is fine; writer will shift if needed
    }
}

private class DagGameTreeBuilder(private val ir: GameIR) {
    private val dag: ActionDag = ir.dag
    private val strategicPlayers: Set<RoleId> = ir.roles
    private val chancePlayers: Set<RoleId> = ir.chanceRoles
    private val infosets = InfosetManager(strategicPlayers)

    fun build(): GameTree {
        val frontier = FrontierMachine.from(dag)
        val initialState = Infoset()
        val initialKnowledge: KnowledgeMap =
            (ir.roles + ir.chanceRoles).associateWith { Infoset() }
        return buildFromFrontier(frontier, initialState, initialKnowledge)
    }

    private fun buildFromFrontier(
        frontier: FrontierMachine<ActionId>,
        state: State,
        knowledgeMap: KnowledgeMap,
    ): GameTree {
        // Terminal: no more actions
        if (frontier.isComplete()) {
            val pay = ir.payoffs.mapValues { (_, e) -> eval(state, e).toOutcome() }
            return GameTree.Terminal(pay)
        }

        val enabled: Set<ActionId> = frontier.enabled()
        require(enabled.isNotEmpty()) {
            "Frontier has no enabled actions but is not complete"
        }

        // Actions enabled at this frontier, grouped per role => simultaneous "pseudo-frontier"
        val actionsByRole: Map<RoleId, List<ActionId>> = enabled.groupBy { dag.owner(it) }
        val roleOrder: List<RoleId> = actionsByRole.keys.sortedBy { it.name }

        // Precompute legal explicit packets per role under the same snapshot state.
        val explicitFrontierChoicesByRole: Map<RoleId, List<FrontierSlice>> =
            actionsByRole.mapValues { (role, actions) ->
                enumerateRoleFrontierChoices(role, actions, state, knowledgeMap.getValue(role))
            }

        fun recurse(idx: Int, accFrontier: FrontierSlice): GameTree {
            if (idx == roleOrder.size) {
                // All roles have chosen for this frontier: commit frontier map and advance DAG frontier.
                val newState = Infoset(accFrontier, state)
                val newKnowledge: KnowledgeMap =
                    knowledgeMap.mapValues { (role, info) ->
                        info with redacted(accFrontier, role)
                    }

                var nextFrontier = frontier
                enabled.forEach {
                    nextFrontier = frontier.resolve(it)
                }
                return buildFromFrontier(nextFrontier, newState, newKnowledge)
            }

            val role = roleOrder[idx]
            val isChanceNode = role in chancePlayers
            val actionsForRole = actionsByRole.getValue(role)
            val allParams = actionsForRole.flatMap { dag.params(it) }

            val explicitFrontierChoices: List<FrontierSlice> =
                explicitFrontierChoicesByRole.getValue(role)

            // Infoset index is a pure function of what this role currently knows.
            val infosetId = infosets.getInfosetNumber(role, knowledgeMap.getValue(role))

            // 1. Explicit choices (non-bail).
            val explicitChoices: List<GameTree.Choice> =
                explicitFrontierChoices.map { frontierDelta ->
                    val subtree = recurse(idx + 1, accFrontier + frontierDelta)

                    // Label only this role's non-Quit fields.
                    // Keep Hidden wrapper for commitments so Gambit GUI shows the flow.
                    val actionLabel: Map<VarId, IrVal> =
                        frontierDelta
                            .filterKeys { fr -> fr.role == role }
                            .filterValues { v -> v != IrVal.Quit }
                            .mapKeys { (fr, _) -> fr.param }

                    GameTree.Choice(
                        action = actionLabel,
                        subtree = subtree,
                        probability = null, // set below for chance
                    )
                }

            val uniformProb: Rational? =
                if (isChanceNode && explicitChoices.isNotEmpty())
                    Rational(1, explicitChoices.size)
                else null

            val explicitWithProb =
                if (isChanceNode)
                    explicitChoices.map { c -> c.copy(probability = uniformProb) }
                else
                    explicitChoices

            // 2. Bail choice for strategic roles (None on all params).
            val allChoices: List<GameTree.Choice> =
                if (isChanceNode) {
                    explicitWithProb
                } else {
                    val bailFrontier: FrontierSlice =
                        if (allParams.isEmpty()) {
                            emptyMap()
                        } else {
                            actionsForRole
                                .flatMap { actionId ->
                                    dag.params(actionId).map { p ->
                                        FieldRef(role, p.name) to IrVal.Quit
                                    }
                                }
                                .toMap()
                        }

                    val bailChoice = GameTree.Choice(
                        action = emptyMap(), // shows as "Quit" / unlabeled move
                        subtree = recurse(idx + 1, accFrontier + bailFrontier),
                        probability = null,
                    )

                    explicitWithProb + bailChoice
                }

            if (allChoices.isEmpty()) {
                throw StaticError("No choices for role $role at frontier")
            }

            // Structural frontier: this role has no parameters at all here.
            // No real decision -> no node; just pick the (unique) subtree.
            if (allParams.isEmpty()) {
                return allChoices.first().subtree
            }

            return GameTree.Decision(
                owner = role,
                infosetId = infosetId,
                choices = allChoices,
                isChance = isChanceNode,
            )
        }

        return recurse(0, emptyMap())
    }

    /**
     * Enumerate all explicit (non-bail) joint packets for a role across all
     * its actions in the current frontier, as a list of FrontierSlice deltas.
     */
    private fun enumerateRoleFrontierChoices(
        role: RoleId,
        actions: List<ActionId>,
        state: State,
        playerKnowledge: Infoset,
    ): List<FrontierSlice> {
        // Once a role has bailed (some field Quit), it has no explicit choices anymore.
        if (state.quit(role)) return emptyList()

        if (actions.isEmpty()) return listOf(emptyMap())

        // For each action, enumerate its local packets.
        val perActionPackets: List<List<Map<VarId, IrVal>>> =
            actions.map { actionId ->
                enumeratePacketsForAction(actionId, state, playerKnowledge)
            }

        if (perActionPackets.any { it.isEmpty() }) return emptyList()

        // Cross-product over actions; then flatten into a single FrontierSlice.
        val combinations: List<List<Map<VarId, IrVal>>> = cartesian(perActionPackets)

        return combinations.map { pktList ->
            val frontierSlice = mutableMapOf<FieldRef, IrVal>()
            actions.zip(pktList).forEach { (actionId, pkt) ->
                val struct: ActionStruct = dag.struct(actionId)
                pkt.forEach { (v, value) ->
                    val field = FieldRef(struct.role, v)
                    // If two actions write the same field, last-in-wins; IR should avoid that.
                    frontierSlice[field] = value
                }
            }
            frontierSlice.toMap()
        }
    }

    /**
     * Enumerate packets for a single action under the current global state.
     * Commit/reveal semantics:
     *  - COMMIT: pick from type domain, store as Hidden(base).
     *  - REVEAL: if prior value is Hidden(x), then only choice is x (as visible value);
     *            otherwise, no legal choice.
     *  - PUBLIC: pick from type domain, store as visible value.
     *
     * Guards are evaluated with the packet layered on top of the player's knowledge.
     */
    private fun enumeratePacketsForAction(
        actionId: ActionId,
        state: State,
        playerKnowledge: Infoset,
    ): List<Map<VarId, IrVal>> {
        val struct: ActionStruct = dag.struct(actionId)
        val spec: ActionSpec = dag.spec(actionId)
        val role = struct.role

        if (spec.params.isEmpty()) return listOf(emptyMap())
        if (state.quit(role)) return emptyList()

        val lists: List<List<Pair<VarId, IrVal>>> = spec.params.map { param ->
            val fieldRef = FieldRef(role, param.name)
            val prior = state.get(fieldRef)
            val vis = struct.visibility.getValue(fieldRef)

            val baseDomain: List<IrVal> = when (vis) {
                Visibility.REVEAL ->
                    when (prior) {
                        is IrVal.Hidden -> listOf(prior.inner)
                        else -> emptyList()
                    }

                Visibility.PUBLIC, Visibility.COMMIT ->
                    when (param.type) {
                        is Type.BoolType ->
                            listOf(IrVal.BoolVal(true), IrVal.BoolVal(false))

                        is Type.SetType ->
                            param.type.values.sorted().map { v -> IrVal.IntVal(v) }

                        is Type.IntType ->
                            throw StaticError("Cannot enumerate IntType; use SetType or BoolType")
                    }
            }

            // The packet we STORE in the frontier must respect visibility (Hidden)
            val domainWithVis: List<IrVal> = when (vis) {
                Visibility.COMMIT -> baseDomain.map { v -> IrVal.Hidden(v) }
                Visibility.PUBLIC, Visibility.REVEAL -> baseDomain
            }

            domainWithVis.map { v -> param.name to v }
        }

        val rawPackets: List<Map<VarId, IrVal>> =
            cartesian(lists).map { it.toMap() }

        // Guard: evaluated on player's knowledge with this action's packet overlayed.
        return rawPackets.filter { pkt ->
            // Unwrap Hidden values for the actor's own guard evaluation.
            // The player knows what they are choosing right now.
            val unwrappedPkt = pkt.mapValues { (_, v) ->
                if (v is IrVal.Hidden) v.inner else v
            }

            val tempHeap = Infoset(toFrontierMap(role, unwrappedPkt), playerKnowledge)
            eval(tempHeap, spec.guardExpr).asBool()
        }
    }

    private fun <T> cartesian(lists: List<List<T>>): List<List<T>> =
        lists.fold(listOf(emptyList())) { acc, xs ->
            acc.flatMap { a -> xs.map { x -> a + x } }
        }
}

internal sealed class IrVal {
    data class IntVal(val v: Int) : IrVal()
    data class BoolVal(val v: Boolean) : IrVal()
    data class Hidden(val inner: IrVal) : IrVal()   // value chosen but not visible to others
    object Opaque : IrVal()  // commitment made but value hidden from observer
    object Quit : IrVal()  // bail/abandonment

    fun toOutcome(): IntVal = when (this) {
        is IntVal -> IntVal(v)
        is BoolVal -> IntVal(if (v) 1 else 0)
        is Hidden, Opaque, Quit -> error("Terminal payoff references undefined/hidden value")
    }

    fun asBool(): Boolean = when (this) {
        is BoolVal -> v
        is IntVal -> v != 0
        is Hidden, Opaque, Quit -> false
    }

    fun asInt(): Int = when (this) {
        is IntVal -> v
        is BoolVal -> if (v) 1 else 0
        is Hidden, Opaque, Quit -> error("Expected int, got $this")
    }
}

private fun eval(heap: Infoset, e: Expr): IrVal {
    fun get(field: FieldRef): IrVal = heap.get(field)

    fun eq(a: IrVal, b: IrVal): Boolean = when {
        a is IrVal.IntVal && b is IrVal.IntVal -> a.v == b.v
        a is IrVal.BoolVal && b is IrVal.BoolVal -> a.v == b.v
        a is IrVal.Quit && b is IrVal.Quit -> true
        else -> false
    }

    fun eval0(x: Expr): IrVal = when (x) {
        is Expr.Const.IntVal -> IrVal.IntVal(x.v)
        is Expr.Const.BoolVal -> IrVal.BoolVal(x.v)
        is Expr.Field -> get(x.field)
        is Expr.IsDefined -> {
            val v = get(x.field)
            IrVal.BoolVal(v !is IrVal.Quit && v !is IrVal.Hidden && v !is IrVal.Opaque)
        }

        // arithmetic
        is Expr.Add -> IrVal.IntVal(eval0(x.l).asInt() + eval0(x.r).asInt())
        is Expr.Sub -> IrVal.IntVal(eval0(x.l).asInt() - eval0(x.r).asInt())
        is Expr.Mul -> IrVal.IntVal(eval0(x.l).asInt() * eval0(x.r).asInt())
        is Expr.Div -> IrVal.IntVal(eval0(x.l).asInt() / eval0(x.r).asInt())
        is Expr.Neg -> IrVal.IntVal(-eval0(x.x).asInt())

        // comparisons
        is Expr.Eq -> IrVal.BoolVal(eq(eval0(x.l), eval0(x.r)))
        is Expr.Ne -> IrVal.BoolVal(!eq(eval0(x.l), eval0(x.r)))
        is Expr.Lt -> IrVal.BoolVal(eval0(x.l).asInt() < eval0(x.r).asInt())
        is Expr.Le -> IrVal.BoolVal(eval0(x.l).asInt() <= eval0(x.r).asInt())
        is Expr.Gt -> IrVal.BoolVal(eval0(x.l).asInt() > eval0(x.r).asInt())
        is Expr.Ge -> IrVal.BoolVal(eval0(x.l).asInt() >= eval0(x.r).asInt())

        // boolean
        is Expr.And -> IrVal.BoolVal(eval0(x.l).asBool() && eval0(x.r).asBool())
        is Expr.Or -> IrVal.BoolVal(eval0(x.l).asBool() || eval0(x.r).asBool())
        is Expr.Not -> IrVal.BoolVal(!eval0(x.x).asBool())
        is Expr.Ite -> if (eval0(x.c).asBool()) eval0(x.t) else eval0(x.e)
    }

    return eval0(e)
}

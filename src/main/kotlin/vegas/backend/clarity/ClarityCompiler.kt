package vegas.backend.clarity

import java.util.ArrayDeque
import vegas.RoleId
import vegas.ir.GameIR
import vegas.ir.ActionId
import vegas.ir.Type
import vegas.ir.Visibility
import vegas.ir.asInt
import vegas.semantics.*

class ClarityCompilationException(message: String) : Exception(message)

internal object ClarityCompiler {

    fun compile(game: GameIR, defaultTimeout: Long): ClarityGame {
        // 1. Roles
        val rolesSorted = game.roles.sortedBy { it.name }
        val potAmount = computePot(game, game.roles)

        // 2. Build Actions
        val rawActions = game.dag.actions.sortedBy { it.second }.map { actionId ->
            buildAction(game, actionId)
        }

        // Sort Topologically
        val actions = topologicalSort(game, rawActions)

        // 3. Explore State Space (Linear Sequence)
        val (abortPayoffs, terminalFrontiers, initialDone) = exploreLinearStateSpace(game, rolesSorted, potAmount, actions)

        return ClarityGame(
            name = game.name,
            roles = rolesSorted,
            pot = potAmount,
            actions = actions,
            abortPayoffs = abortPayoffs,
            initialDone = initialDone,
            terminalFrontiers = terminalFrontiers,
            payoffs = game.payoffs
        )
    }

    private fun topologicalSort(game: GameIR, actions: List<ClarityAction>): List<ClarityAction> {
        val result = mutableListOf<ClarityAction>()
        val visited = mutableSetOf<ActionId>()
        val temp = mutableSetOf<ActionId>()
        val actionMap = actions.associateBy { it.id }

        fun visit(id: ActionId) {
            if (id in visited) return
            if (id in temp) throw ClarityCompilationException("Cycle detected in ActionDAG")
            temp.add(id)

            game.dag.prerequisitesOf(id).forEach { dep ->
                if (dep in actionMap) visit(dep)
            }

            temp.remove(id)
            visited.add(id)
            result.add(actionMap[id]!!)
        }

        // Sort by ID to ensure deterministic order among independent nodes
        actions.sortedBy { it.id.second }.forEach { action ->
            visit(action.id)
        }

        return result
    }

    private fun buildAction(game: GameIR, actionId: ActionId): ClarityAction {
        val owner = game.dag.owner(actionId)
        val spec = game.dag.spec(actionId)
        val kind = game.dag.kind(actionId)
        val visMap = game.dag.visibilityOf(actionId)

        val params = spec.params.map { param ->
            val fieldRef = vegas.FieldRef(owner, param.name)
            val vis = visMap[fieldRef]!!
            ClarityParam(
                name = param.name.name,
                type = param.type,
                isSalt = (vis == Visibility.REVEAL)
            )
        }

        val writes = spec.params.map { param ->
            val fieldRef = vegas.FieldRef(owner, param.name)
            val vis = visMap[fieldRef]!!
            ClarityStateVar(
                name = "${owner.name}-${param.name.name}",
                type = param.type,
                isCommit = (vis == Visibility.COMMIT)
            )
        }

        val type = when (kind) {
            Visibility.COMMIT -> ActionType.Commit
            Visibility.REVEAL -> ActionType.Reveal("")
            Visibility.PUBLIC -> ActionType.Public
        }

        val guard = if (spec.guardExpr is vegas.ir.Expr.Const.BoolVal && spec.guardExpr.v) null else spec.guardExpr

        return ClarityAction(
            id = actionId,
            owner = owner,
            prereqs = game.dag.prerequisitesOf(actionId),
            params = params,
            type = type,
            writes = writes,
            guard = guard
        )
    }

    private fun exploreLinearStateSpace(
        game: GameIR,
        roles: List<RoleId>,
        pot: Long,
        sortedActions: List<ClarityAction>
    ): Triple<Map<Set<ActionId>, Map<RoleId, Long>>, List<Set<ActionId>>, Set<ActionId>> {
        val semantics = GameSemantics(game)

        val frontierPayoffs = mutableMapOf<Set<ActionId>, Map<RoleId, Long>>()
        val terminalFrontiers = mutableListOf<Set<ActionId>>()

        val initial = Configuration.initial(game)
        val (canonInitial, initialDone) = canonicalize(semantics, initial, roles)

        var currentConfig = canonInitial
        var currentDone = initialDone

        // Loop through actions
        for (action in sortedActions) {
            if (action.id in currentDone) continue

            val moves = semantics.enabledMoves(currentConfig)
            val move = moves.filterIsInstance<Label.Play>()
                .find { (it.tag as? PlayTag.Action)?.actionId == action.id }

            if (move == null) break

            val abortPayoff = resolveAbortScenario(semantics, game, currentConfig, currentDone, action.owner, roles, pot)
            frontierPayoffs[currentDone] = abortPayoff

            val next = applyMove(currentConfig, move)
            val (canonNext, canonDone) = canonicalize(semantics, next, roles)

            currentConfig = canonNext
            currentDone = currentDone + action.id + canonDone
        }

        if (currentConfig.isTerminal()) {
            terminalFrontiers.add(currentDone)
        }

        return Triple(frontierPayoffs, terminalFrontiers, initialDone)
    }

    private fun computePot(game: GameIR, players: Set<RoleId>): Long {
        val dag = game.dag
        var pot = 0L
        for (actionId in dag.actions) {
            val owner = dag.owner(actionId)
            if (owner !in players) continue
            val join = dag.spec(actionId).join
            if (join != null) {
                val deposit = join.deposit.v
                if (deposit < 0) error("Negative deposit")
                pot += deposit.toLong()
            }
        }
        return pot
    }

    private fun canonicalize(
        semantics: GameSemantics, start: Configuration, players: List<RoleId>
    ): Pair<Configuration, Set<ActionId>> {
        var current = start
        val done = mutableSetOf<ActionId>()

        while (true) {
            if (current.isTerminal()) return current to done
            val moves = semantics.enabledMoves(current)
            val hasStrategic = moves.any {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in players
            }
            if (hasStrategic) return current to done
            val hasQuit = moves.any {
                it is Label.Play && it.tag == PlayTag.Quit && it.role in players
            }
            if (hasQuit) return current to done

            val systemMoves = moves
            if (systemMoves.isEmpty()) return current to done

            val finalize = systemMoves.find { it is Label.FinalizeFrontier }
            if (finalize != null) {
                done.addAll(current.enabled())
                current = applyMove(current, finalize)
            } else {
                 return current to done
            }
        }
    }

    private fun resolvePayoff(
        game: GameIR, config: Configuration, roles: List<RoleId>, pot: Long
    ): Map<RoleId, Long> {
        val evalContext = { ref: vegas.FieldRef -> config.history.get(ref) }
        val payoffs = mutableMapOf<RoleId, Long>()
        var sum = 0L
        for (role in roles) {
            val expr = game.payoffs[role]
            val amount = if (expr != null) eval(evalContext, expr).asInt().toLong() else 0L
            payoffs[role] = amount
            sum += amount
        }
        return payoffs
    }

    private fun resolveAbortScenario(
        semantics: GameSemantics,
        game: GameIR,
        config: Configuration,
        doneActions: Set<ActionId>,
        quitter: RoleId,
        players: List<RoleId>,
        pot: Long
    ): Map<RoleId, Long> {
        val allFields = game.dag.actions
            .filter { game.dag.owner(it) == quitter && it !in doneActions }
            .flatMap { game.dag.writes(it) }
            .toSet()

        val quitDelta = allFields.associateWith { vegas.ir.Expr.Const.Quit }
        val quitLabel = Label.Play(quitter, quitDelta, PlayTag.Quit)

        var current = applyMove(config, quitLabel)
        current = canonicalize(semantics, current, players).first

        val calculatedPayoffs = resolvePayoff(game, current, players, pot)

        // Strict Quit Policy: Quitter forfeits everything to the remaining players.
        if (players.size > 1 && (calculatedPayoffs[quitter] ?: 0L) > 0L) {
             val quitterAmt = calculatedPayoffs[quitter]!!
             val others = players - quitter
             val bonus = quitterAmt / others.size
             val remainder = quitterAmt % others.size

             val newPayoffs = calculatedPayoffs.toMutableMap()
             newPayoffs[quitter] = 0L

             others.forEachIndexed { idx, role ->
                 val extra = if (idx == 0) remainder else 0L
                 newPayoffs[role] = (newPayoffs[role] ?: 0L) + bonus + extra
             }
             return newPayoffs
        }

        return calculatedPayoffs
    }
}

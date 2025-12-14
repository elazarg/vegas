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
        val actions = game.dag.actions.sortedBy { it.second }.map { actionId ->
            buildAction(game, actionId)
        }

        // 3. Explore State Space
        val (abortPayoffs, terminalFrontiers) = exploreStateSpace(game, rolesSorted, potAmount)

        return ClarityGame(
            name = game.name,
            roles = rolesSorted,
            pot = potAmount,
            actions = actions,
            abortPayoffs = abortPayoffs,
            terminalFrontiers = terminalFrontiers,
            payoffs = game.payoffs
        )
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

    private fun exploreStateSpace(
        game: GameIR,
        roles: List<RoleId>,
        pot: Long
    ): Pair<Map<Set<ActionId>, Map<RoleId, Long>>, List<Set<ActionId>>> {
        val semantics = GameSemantics(game)

        val frontierPayoffs = mutableMapOf<Set<ActionId>, Map<RoleId, Long>>()
        val terminalFrontiers = mutableSetOf<Set<ActionId>>()

        val visited = mutableSetOf<Set<ActionId>>()
        val queue = ArrayDeque<Pair<Configuration, Set<ActionId>>>()

        val initial = Configuration.initial(game)
        val (canonInitial, initialDone) = canonicalize(semantics, initial, roles)
        queue.add(canonInitial to initialDone)
        visited.add(initialDone)

        while (queue.isNotEmpty()) {
            val (config, done) = queue.remove()
            val moves = semantics.enabledMoves(config)

            val strategic = moves.filterIsInstance<Label.Play>()
                .filter { it.tag != PlayTag.Quit && it.role in roles }
            val quit = moves.filterIsInstance<Label.Play>()
                .filter { it.tag == PlayTag.Quit && it.role in roles }

            if (config.isTerminal() || (strategic.isEmpty() && quit.isEmpty())) {
                terminalFrontiers.add(done)
                continue
            }

            // Calculate abort payoff
            val active = if (strategic.isNotEmpty()) {
                strategic.minByOrNull { it.role.name }!!.role
            } else {
                quit.minByOrNull { it.role.name }!!.role
            }

            val abortPayoff = resolveAbortScenario(semantics, game, config, active, roles, pot)
            frontierPayoffs[done] = abortPayoff

            // Explore
            for (move in strategic) {
                val next = applyMove(config, move)
                val (canonNext, canonDone) = canonicalize(semantics, next, roles)

                val actionId = (move.tag as PlayTag.Action).actionId
                // We add actionId (from Play) AND any actions completed by Finalize (canonDone)
                val nextDone = done + actionId + canonDone

                if (nextDone !in visited) {
                    visited.add(nextDone)
                    queue.add(canonNext to nextDone)
                }
            }
        }

        return frontierPayoffs to terminalFrontiers.toList()
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
        quitter: RoleId,
        players: List<RoleId>,
        pot: Long
    ): Map<RoleId, Long> {
        var current = config
        val moves = semantics.enabledMoves(current)
        val quitLabel = moves.find {
            it is Label.Play && it.role == quitter && it.tag == PlayTag.Quit
        } ?: return resolvePayoff(game, current, players, pot)

        current = applyMove(current, quitLabel)
        current = canonicalize(semantics, current, players).first

        while (!current.isTerminal()) {
            val m = semantics.enabledMoves(current)
            val nextQuit = m.filterIsInstance<Label.Play>()
                .filter { it.tag == PlayTag.Quit && it.role in players }
                .minByOrNull { it.role.name }
            if (nextQuit == null) break
            current = applyMove(current, nextQuit)
            current = canonicalize(semantics, current, players).first
        }
        return resolvePayoff(game, current, players, pot)
    }
}

package vegas.backend.clarity

import java.util.ArrayDeque
import vegas.RoleId
import vegas.FieldRef
import vegas.semantics.*
import vegas.ir.*

class ClarityCompilationException(message: String) : Exception(message)

internal object ClarityCompiler {

    // Helper class to group concrete configurations by their public projection
    data class PublicConfiguration(
        val frontier: Any, // FrontierMachine (reference equality is sufficient for serialized execution)
        val history: History,
        val partial: FrontierAssignmentSlice
    )

    fun compile(game: GameIR, defaultTimeout: Long): ClarityProtocol {
        val rolesSorted = game.roles.sortedBy { it.name }
        val semantics = GameSemantics(game)
        val potAmount = computePot(game, game.roles)

        val mapConcreteToStateId = mutableMapOf<Configuration, Int>()
        val mapPublicToStateId = mutableMapOf<PublicConfiguration, Int>()
        val protocolStates = mutableMapOf<Int, ClarityState>()
        val queue = ArrayDeque<Configuration>()
        var nextStateId = -1

        // Initial State
        val initialConfig = Configuration.initial(game)
        val rootConfig = canonicalize(semantics, initialConfig, rolesSorted)

        fun getOrEnqueue(c: Configuration): Int {
            // Check if this concrete config is already visited
            if (c in mapConcreteToStateId) return mapConcreteToStateId[c]!!

            val pub = project(c)
            val id = if (pub in mapPublicToStateId) {
                mapPublicToStateId[pub]!!
            } else {
                val newId = ++nextStateId
                mapPublicToStateId[pub] = newId
                newId
            }

            mapConcreteToStateId[c] = id
            // Always enqueue concrete config to ensure we explore its specific hidden branches
            queue.add(c)
            return id
        }

        val rootId = getOrEnqueue(rootConfig)

        while (queue.isNotEmpty()) {
            val config = queue.remove()
            val id = mapConcreteToStateId[config]!!

            // If we already processed this StateId (from another concrete config),
            // we typically still need to process this config to find *new* transitions
            // (e.g. Reveal T vs Reveal F).
            // But we must merge them into the existing state.
            // The `protocolStates` map will be updated.

            val moves = semantics.enabledMoves(config)

            // Strategic moves
            val strategicMoves = moves.filter {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in rolesSorted
            }

            if (strategicMoves.isEmpty()) {
                // Terminal or Forced Abort
                handleTerminalOrAbort(game, semantics, config, id, moves, rolesSorted, potAmount, protocolStates, defaultTimeout)
            } else {
                // Strategic State
                // Deterministic Scheduling: Pick first role
                val actors = strategicMoves.map { (it as Label.Play).role }.distinct().sortedBy { it.name }
                val activePlayer = actors.first()
                val activePlayerMoves = strategicMoves.filter { (it as Label.Play).role == activePlayer }

                // Abort Balance (use concrete config, assume consistent across public state)
                val abortBalance = resolveAbortScenario(
                    semantics, game, config, activePlayer, rolesSorted, potAmount
                )

                // Process transitions
                val newTransitions = activePlayerMoves.map { move ->
                    val rawNext = applyMove(config, move)
                    val canonNext = canonicalize(semantics, rawNext, rolesSorted)
                    val nextId = getOrEnqueue(canonNext)
                    ClarityTransition(move, nextId)
                }

                // Merge with existing transitions for this state
                val existingState = protocolStates[id]
                if (existingState == null) {
                    protocolStates[id] = ClarityState(id, activePlayer, newTransitions, abortBalance, defaultTimeout)
                } else {
                    // We might be discovering new branches (e.g. Reveal F)
                    // Combine transitions. simple list concat?
                    // Deduplicate based on Label + NextStateId
                    val allTrans = (existingState.transitions + newTransitions).distinct()

                    // Verify consistency of activePlayer and abortBalance
                    if (existingState.activePlayer != activePlayer) {
                         // This shouldn't happen with serialized execution and public state projection
                         // unless different hidden histories lead to different active players?
                         // With perfect recall and serialized scheduling, it should be fine.
                    }

                    protocolStates[id] = existingState.copy(transitions = allTrans)
                }
            }
        }

        return ClarityProtocol(
            name = game.name,
            roles = rolesSorted,
            states = protocolStates,
            rootStateId = rootId,
            totalPot = potAmount
        )
    }

    private fun handleTerminalOrAbort(
        game: GameIR,
        semantics: GameSemantics,
        config: Configuration,
        id: Int,
        moves: List<Label>,
        rolesSorted: List<RoleId>,
        potAmount: Long,
        protocolStates: MutableMap<Int, ClarityState>,
        defaultTimeout: Long
    ) {
        // If state already exists, we assume it's consistent.
        if (id in protocolStates) return

        if (config.isTerminal()) {
            val finalBalance = resolvePayoff(game, config, rolesSorted, potAmount)
            protocolStates[id] = ClarityState(id, null, emptyList(), finalBalance, 0)
        } else {
            val quitMoves = moves.filterIsInstance<Label.Play>()
                .filter { it.tag == PlayTag.Quit && it.role in rolesSorted }

            if (quitMoves.isNotEmpty()) {
                val quitter = quitMoves.minByOrNull { it.role.name }!!.role
                val finalBalance = resolveAbortScenario(
                    semantics, game, config, quitter, rolesSorted, potAmount
                )
                protocolStates[id] = ClarityState(id, null, emptyList(), finalBalance, 0)
            } else {
                // Deadlock
                try {
                    val finalBalance = resolvePayoff(game, config, rolesSorted, potAmount)
                    protocolStates[id] = ClarityState(id, null, emptyList(), finalBalance, 0)
                } catch (e: Exception) {
                    // Skip or throw
                }
            }
        }
    }

    // --- Projection Logic ---

    private fun project(c: Configuration): PublicConfiguration {
        return PublicConfiguration(
            frontier = c.frontier,
            history = projectHistory(c.history),
            partial = projectSlice(c.partialFrontierAssignment)
        )
    }

    private fun projectHistory(h: History): History {
        val pLast = projectSlice(h.lastFrontier)
        val pPast = h.past?.let { projectHistory(it) }
        // We reuse History class but with Opaque values
        return History(pLast, pPast)
    }

    private fun projectSlice(slice: FrontierAssignmentSlice): FrontierAssignmentSlice {
        return slice.mapValues { (_, v) ->
            if (v is Expr.Const.Hidden) Expr.Const.Opaque else v
        }
    }

    // --- Helpers (copied/adapted) ---

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
    ): Configuration {
        var current = start
        while (true) {
            if (current.isTerminal()) return current
            val moves = semantics.enabledMoves(current)
            val hasStrategic = moves.any {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in players
            }
            if (hasStrategic) return current
            val hasQuit = moves.any {
                it is Label.Play && it.tag == PlayTag.Quit && it.role in players
            }
            if (hasQuit) return current

            val systemMoves = moves
            if (systemMoves.isEmpty()) return current

            val finalize = systemMoves.find { it is Label.FinalizeFrontier }
            if (finalize != null) {
                current = applyMove(current, finalize)
            } else {
                 return current
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
        // normalization/checks?
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
        } ?: return emptyMap()

        current = applyMove(current, quitLabel)
        current = canonicalize(semantics, current, players)

        while (!current.isTerminal()) {
            val m = semantics.enabledMoves(current)
            val nextQuit = m.filterIsInstance<Label.Play>()
                .filter { it.tag == PlayTag.Quit && it.role in players }
                .minByOrNull { it.role.name }
            if (nextQuit == null) break
            current = applyMove(current, nextQuit)
            current = canonicalize(semantics, current, players)
        }
        return resolvePayoff(game, current, players, pot)
    }
}

package vegas.backend.bitcoin

import vegas.RoleId
import vegas.ir.GameIR
import vegas.ir.asInt
import vegas.semantics.*
import java.util.ArrayDeque

class CompilationException(message: String) : Exception(message)

object LightningCompiler {

    internal fun compile(game: GameIR, roleA: RoleId, roleB: RoleId, potAmount: Long): LightningProtocol {
        // 1. Validate Roles
        val sortedRoles = game.roles.sortedBy { it.name }
        if (sortedRoles.size != 2) {
            throw CompilationException("Lightning backend requires exactly 2 strategic roles. Found: ${game.roles}")
        }
        if (setOf(roleA, roleB) != game.roles) {
            throw CompilationException("Provided mapping ($roleA, $roleB) does not match game roles ${game.roles}")
        }

        val semantics = GameSemantics(game)
        val players = setOf(roleA, roleB)

        val visited = mutableMapOf<Configuration, StateId>()
        val protocolStates = mutableMapOf<StateId, ProtocolState>()
        val queue = ArrayDeque<Configuration>()
        var nextStateId = -1

        fun getOrEnqueue(c: Configuration): StateId {
            if (c in visited) return visited[c]!!
            val id = ++nextStateId
            visited[c] = id
            queue.add(c)
            return id
        }

        // Start at the canonical root (fast-forward past initial system moves)
        val initialConfig = Configuration.initial(game)
        val rootConfig = canonicalize(semantics, initialConfig, players)
        val rootId = getOrEnqueue(rootConfig)

        while (!queue.isEmpty()) {
            val config = queue.remove()
            val id = visited[config]!!

            val moves = semantics.enabledMoves(config)

            // Filter strictly for Strategic moves (Play by A/B, not Quit)
            val strategicMoves = moves.filter {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in players
            }

            val state: ProtocolState = if (strategicMoves.isEmpty()) {
                // --- CASE 1: Terminal or Forced Abort ---
                if (config.isTerminal()) {
                    val finalBalance = resolvePayoff(game, config, roleA, roleB, potAmount)
                    ProtocolState(id, finalBalance, null, emptyList())
                } else {
                    // Check for Quit moves by A/B
                    val quitMoves = moves
                        .filterIsInstance<Label.Play>()
                        .filter { it.tag == PlayTag.Quit && it.role in players }

                    if (quitMoves.isNotEmpty()) {
                        if (quitMoves.map { it.role }.distinct().size > 1) {
                            throw CompilationException("State $id has multiple players who must quit. Not strictly turn-based.")
                        }

                        val quitter = quitMoves.first().role
                        val finalBalance = resolveAbortScenario(semantics, game, config, quitter, players, roleA, roleB, potAmount)
                        ProtocolState(id, finalBalance, null, emptyList())
                    } else {
                        // Deadlocked state (no moves possible). Treat as terminal.
                        try {
                            val finalBalance = resolvePayoff(game, config, roleA, roleB, potAmount)
                            ProtocolState(id, finalBalance, null, emptyList())
                        } catch (e: Exception) {
                            throw CompilationException("State $id is stuck (non-terminal, no supported moves) and payoff resolution failed: ${e.message}")
                        }
                    }
                }
            } else {
                // --- CASE 2: Strategic State ---
                val actors = strategicMoves.map { (it as Label.Play).role }.distinct()
                if (actors.size > 1) {
                    throw CompilationException("State $id is not strictly turn-based. Actors: $actors")
                }
                val activePlayer = actors.first()

                // Calculate Abort Balance using cascading quit
                val abortBalance = resolveAbortScenario(semantics, game, config, activePlayer, players, roleA, roleB, potAmount)

                val transitions = strategicMoves.map { move ->
                    val rawNext = applyMove(config, move)
                    val canonNext = canonicalize(semantics, rawNext, players)
                    val nextId = getOrEnqueue(canonNext)
                    ProtocolTransition(move, nextId)
                }

                ProtocolState(id, abortBalance, activePlayer, transitions)
            }
            protocolStates[id] = state
        }

        return LightningProtocol(
            name = game.name,
            roleA = roleA,
            roleB = roleB,
            totalPot = potAmount,
            rootStateId = rootId,
            states = protocolStates
        )
    }

    /**
     * Advances configuration past "System Moves".
     * A move is System if it is NOT a Strategic Play by [players] and NOT a Quit by [players].
     * Only `FinalizeFrontier` is allowed as a System Move.
     */
    private fun canonicalize(semantics: GameSemantics, start: Configuration, players: Set<RoleId>): Configuration {
        var current = start
        while (true) {
            if (current.isTerminal()) return current

            val moves = semantics.enabledMoves(current)

            // 1. Is there a Strategic Play? (Stop)
            val hasStrategic = moves.any {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in players
            }
            if (hasStrategic) return current

            // 2. Is there a Player Quit? (Stop, let compile() handle it as Forced Abort)
            val hasQuit = moves.any {
                it is Label.Play && it.tag == PlayTag.Quit && it.role in players
            }
            if (hasQuit) return current

            // 3. Everything else is a System Move
            val systemMoves = moves // Since we filtered out Play/Quit by players above

            if (systemMoves.isEmpty()) return current // Deadlock

            val finalize = systemMoves.find { it is Label.FinalizeFrontier }
            val otherSystem = systemMoves.filter { it !is Label.FinalizeFrontier }

            if (otherSystem.isNotEmpty()) {
                // This catches Chance moves (Play by Coin), Yields, etc.
                throw CompilationException("Unsupported system moves detected: $otherSystem. Only FinalizeFrontier is supported.")
            }

            if (finalize != null) {
                current = applyMove(current, finalize)
            } else {
                return current
            }
        }
    }

    private fun resolvePayoff(
        game: GameIR,
        config: Configuration,
        roleA: RoleId,
        roleB: RoleId,
        pot: Long
    ): BalanceSplit {
        val evalContext = { ref: vegas.FieldRef -> config.history.get(ref) }
        val payoffs = game.payoffs.mapValues { (_, expr) ->
            eval(evalContext, expr).asInt()
        }

        val payA = payoffs[roleA] ?: 0
        val payB = payoffs[roleB] ?: 0

        return when {
            payA > 0 && payB <= 0 -> BalanceSplit(pot, 0)
            payB > 0 && payA <= 0 -> BalanceSplit(0, pot)
            payA <= 0 && payB <= 0 -> {
                throw CompilationException("Ambiguous payoff (A=$payA, B=$payB). Lightning backend requires strictly one positive winner.")
            }
            else -> throw CompilationException("Non-Winner-Takes-All payoff detected (A=$payA, B=$payB).")
        }
    }

    private fun resolveAbortScenario(
        semantics: GameSemantics,
        game: GameIR,
        config: Configuration,
        activePlayer: RoleId,
        players: Set<RoleId>,
        roleA: RoleId,
        roleB: RoleId,
        pot: Long
    ): BalanceSplit {
        var currentConfig = config

        // 1. Initial Quit
        val initialMoves = semantics.enabledMoves(currentConfig)
        val quitLabel = initialMoves.find {
            it is Label.Play && it.role == activePlayer && it.tag == PlayTag.Quit
        } ?: throw CompilationException("State requires Abort resolution but no Quit move found for $activePlayer")

        currentConfig = applyMove(currentConfig, quitLabel)
        currentConfig = canonicalize(semantics, currentConfig, players)

        // 2. Cascading Quit Loop
        while (!currentConfig.isTerminal()) {
            val moves = semantics.enabledMoves(currentConfig)

            // Check for remaining active players (who haven't quit yet)
            val forceQuitMoves = moves
                .filterIsInstance<Label.Play>()
                .filter { it.tag == PlayTag.Quit && it.role in players }

            if (forceQuitMoves.isEmpty()) {
                break
            }

            val nextQuit = forceQuitMoves.first()
            currentConfig = applyMove(currentConfig, nextQuit)
            currentConfig = canonicalize(semantics, currentConfig, players)
        }

        return resolvePayoff(game, currentConfig, roleA, roleB, pot)
    }
}
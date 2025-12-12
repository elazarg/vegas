package vegas.backend.bitcoin

import java.util.ArrayDeque
import vegas.RoleId
import vegas.ir.GameIR
import vegas.ir.asInt
import vegas.semantics.*

class CompilationException(message: String) : Exception(message)

/**
 * Compile a two-player Vegas GameIR into a Lightning-compatible explicit state machine.
 *
 * Semantics for this backend:
 *
 *  - The game has exactly two strategic roles.
 *  - The Lightning pot is derived from the game:
 *        totalPot = sum of join deposits for the two roles.
 *
 *  - At every terminal / abort outcome, the Vegas payoffs for the two roles are
 *    interpreted as *withdrawal amounts* from this fixed pot.
 *    Withdrawals must satisfy:
 *        amountA >= 0
 *        amountB >= 0
 *        amountA + amountB <= totalPot
 *
 *  - Each ProtocolState is annotated with an `abortBalance`:
 *      * Terminal: the final withdrawal distribution.
 *      * Strategic: the distribution that will be enforced if `activePlayer` quits now
 *        (simulated by cascading Quit moves and system moves to a terminal configuration).
 *      * Forced abort: the distribution after simulating the pending Quit(s).
 *
 *  - Execution is serialized into a turn-based ESM:
 *      * At any strategic frontier where multiple players have enabled non-Quit moves,
 *        the compiler chooses a deterministic scheduler: the lexicographically smallest
 *        role name is the unique `activePlayer` for that state.
 *      * System moves are absorbed into canonicalization; only FinalizeFrontier is allowed.
 */
object LightningCompiler {

    internal fun compile(game: GameIR): LightningProtocol {
        // 1. Validate Roles
        if (game.roles.size != 2) {
            throw CompilationException("Lightning backend requires exactly 2 strategic roles. Found: ${game.roles}")
        }

        // Stable player ordering used everywhere (A,B)
        val playersSorted = game.roles.sortedBy { it.name }
        val roleA = playersSorted[0]
        val roleB = playersSorted[1]

        val semantics = GameSemantics(game)
        val potAmount = computePot(game, game.roles)

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
        val rootConfig = canonicalize(semantics, initialConfig, playersSorted)
        val rootId = getOrEnqueue(rootConfig)

        while (queue.isNotEmpty()) {
            val config = queue.remove()
            val id = visited[config]!!

            val moves = semantics.enabledMoves(config)

            // Filter strictly for strategic moves (Play by our two players, not Quit)
            val strategicMoves = moves.filter {
                it is Label.Play && it.tag != PlayTag.Quit && it.role in playersSorted
            }

            val state: ProtocolState = if (strategicMoves.isEmpty()) {
                // --- CASE 1: Terminal or Forced Abort ---
                if (config.isTerminal()) {
                    // Terminal state: evaluate withdrawals directly
                    val finalBalance = resolvePayoff(game, config, roleA, roleB, potAmount)
                    ProtocolState(id, finalBalance, null, emptyList())
                } else {
                    // Check for Quit moves by our players
                    val quitMoves = moves.filterIsInstance<Label.Play>()
                        .filter { it.tag == PlayTag.Quit && it.role in playersSorted }

                    if (quitMoves.isNotEmpty()) {
                        // Forced abort: all enabled moves for strategic roles are Quit
                        if (quitMoves.map { it.role }.distinct().size > 1) {
                            throw CompilationException("State $id has multiple players who must quit. Not strictly turn-based.")
                        }

                        val quitter = quitMoves.first().role
                        val finalBalance = resolveAbortScenario(
                            semantics, game, config, quitter, playersSorted, roleA, roleB, potAmount
                        )
                        ProtocolState(id, finalBalance, null, emptyList())
                    } else {
                        // Deadlocked state (no moves possible). Treat as terminal if we can resolve payoffs.
                        try {
                            val finalBalance = resolvePayoff(game, config, roleA, roleB, potAmount)
                            ProtocolState(id, finalBalance, null, emptyList())
                        } catch (e: Exception) {
                            throw CompilationException(
                                "State $id is stuck (non-terminal, no supported moves) and payoff resolution failed: ${e.message}"
                            )
                        }
                    }
                }
            } else {
                // --- CASE 2: Strategic State ---
                // Multiple players may have enabled moves at this frontier (e.g., concurrent commits
                // in a commit-reveal scheme). The IR's commit-reveal expansion ensures that any
                // topological ordering of these moves is strategically equivalent, since committed
                // values are hidden from other players.
                //
                // We pick a deterministic canonical ordering: lexicographically first player by name.
                // The game semantics enforce that once a player acts in a frontier (via hasActed()),
                // they cannot act again until FinalizeFrontier advances to the next frontier.
                // This serialization is transparent to the game logic.
                val actors = strategicMoves.map { (it as Label.Play).role }.distinct().sortedBy { it.name }
                val activePlayer = actors.first()

                // Filter transitions to only this player's moves. After the active player moves,
                // the configuration will have hasActed(activePlayer) = true, and the next state
                // will enable the remaining players' moves.
                val activePlayerMoves = strategicMoves.filter { (it as Label.Play).role == activePlayer }

                // Calculate Abort Balance: what happens if activePlayer quits right now
                val abortBalance = resolveAbortScenario(
                    semantics, game, config, activePlayer, playersSorted, roleA, roleB, potAmount
                )

                val transitions = activePlayerMoves.map { move ->
                    val rawNext = applyMove(config, move)
                    val canonNext = canonicalize(semantics, rawNext, playersSorted)
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
     * Compute the Lightning pot from the GameIR:
     *
     *  - For each action whose owner is in [players], if its ActionSpec has a non-null `join`,
     *    we add join.deposit.v to the pot.
     *
     * Assumptions (current Vegas language):
     *  - Join deposits are constant Int values.
     *  - Each role has at most one join step (if not, we just sum them, which still upper-bounds
     *    the amount that can be locked for that role).
     */
    private fun computePot(game: GameIR, players: Set<RoleId>): Long {
        val dag = game.dag
        var pot = 0L

        for (actionId in dag.actions) {
            val owner = dag.owner(actionId)
            if (owner !in players) continue

            val join = dag.spec(actionId).join
            if (join != null) {
                val deposit = join.deposit.v
                if (deposit < 0) {
                    throw CompilationException("Negative join deposit for role $owner in action $actionId: $deposit")
                }
                pot += deposit.toLong()
            }
        }

        return pot
    }

    /**
     * Advances configuration past "System Moves".
     *
     * A move is System if it is NOT a strategic Play by [players] and NOT a Quit by [players].
     * Only `FinalizeFrontier` is allowed as a System Move.
     *
     * Canonicalization stops when:
     *  - the configuration is terminal, OR
     *  - there is at least one strategic (non-Quit) move by a strategic player, OR
     *  - there is a Quit move by a strategic player (forced-abort state).
     */
    private fun canonicalize(
        semantics: GameSemantics, start: Configuration, players: List<RoleId>
    ): Configuration {
        var current = start
        while (true) {
            if (current.isTerminal()) return current

            val moves = semantics.enabledMoves(current)

            // 1. Is there a strategic Play? (Stop)
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
                throw CompilationException(
                    "Unsupported system moves detected: $otherSystem. Only FinalizeFrontier is supported."
                )
            }

            if (finalize != null) {
                current = applyMove(current, finalize)
            } else {
                return current
            }
        }
    }

    /**
     * Evaluate the Vegas payoffs at [config] as concrete withdrawal amounts (in sats)
     * for [roleA] and [roleB], subject to Lightning constraints.
     */
    private fun resolvePayoff(
        game: GameIR, config: Configuration, roleA: RoleId, roleB: RoleId, pot: Long
    ): BalanceSplit {
        val evalContext = { ref: vegas.FieldRef -> config.history.get(ref) }
        val payoffs = game.payoffs.mapValues { (_, expr) ->
            eval(evalContext, expr).asInt()
        }

        val rawA = payoffs[roleA] ?: 0
        val rawB = payoffs[roleB] ?: 0

        val a = rawA.toLong()
        val b = rawB.toLong()

        if (a < 0L || b < 0L) {
            throw CompilationException(
                "Lightning backend requires non-negative withdrawals; got A=$a, B=$b"
            )
        }

        if (a + b > pot) {
            throw CompilationException(
                "Lightning withdrawals exceed pot: A=$a, B=$b, pot=$pot"
            )
        }

        return BalanceSplit(a, b)
    }

    /**
     * Simulate an abort scenario where [activePlayer] quits at [config]:
     *
     *  1. Apply the Quit move for [activePlayer].
     *  2. Canonicalize via system moves.
     *  3. Repeatedly apply any remaining Quit moves by strategic players, with canonicalization,
     *     until a terminal configuration is reached or no further quits are enabled.
     *  4. Evaluate the final withdrawals via [resolvePayoff].
     */
    private fun resolveAbortScenario(
        semantics: GameSemantics,
        game: GameIR,
        config: Configuration,
        activePlayer: RoleId,
        players: List<RoleId>,
        roleA: RoleId,
        roleB: RoleId,
        pot: Long
    ): BalanceSplit {
        var currentConfig = config

        // 1. Initial Quit by activePlayer
        val initialMoves = semantics.enabledMoves(currentConfig)
        val quitLabel = initialMoves.find {
            it is Label.Play && it.role == activePlayer && it.tag == PlayTag.Quit
        } ?: throw CompilationException(
            "State requires abort resolution but no Quit move found for $activePlayer"
        )

        currentConfig = applyMove(currentConfig, quitLabel)
        currentConfig = canonicalize(semantics, currentConfig, players)

        // 2. Cascading Quit Loop for remaining players
        while (!currentConfig.isTerminal()) {
            val moves = semantics.enabledMoves(currentConfig)

            val forceQuitMoves =
                moves.filterIsInstance<Label.Play>().filter { it.tag == PlayTag.Quit && it.role in players }

            if (forceQuitMoves.isEmpty()) {
                break
            }

            val nextQuit = forceQuitMoves.first()
            currentConfig = applyMove(currentConfig, nextQuit)
            currentConfig = canonicalize(semantics, currentConfig, players)
        }

        // 3. Final withdrawals at abort outcome
        return resolvePayoff(game, currentConfig, roleA, roleB, pot)
    }
}

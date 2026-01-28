package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import vegas.backend.evm.EvmConstants
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR

/**
 * Model-driven timeout tests: for each game with quit/timeout handlers,
 * systematically test bail-out behavior by advancing Anvil time past TIMEOUT.
 *
 * For each timeout-able action in a game:
 * 1. Play the game up to that action (submitting all prior moves)
 * 2. Advance time past TIMEOUT_SECONDS
 * 3. Continue with remaining actions (which take the bail-out path)
 * 4. Verify contract still executes withdrawals without reverting
 */
@EnabledIf(EthToolsAvailable::class)
class EthTimeoutModelTest : FunSpec({

    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    /**
     * For a given game, enumerate non-quit traces, and for each one, test
     * timing out at each possible point after joins are complete.
     *
     * We play the trace up to move index [timeoutAfter], advance time, then
     * attempt to execute withdrawals. The contract's `depends` modifier
     * should set bailed flags and allow bail-out payoffs.
     */
    fun testTimeoutAt(gameName: String, timeoutAfter: Int) {
        val game = loadGame(gameName)
        val traces = TraceEnumerator.exhaustive(game, maxTraces = 10)

        require(traces.isNotEmpty()) { "No traces found for $gameName" }

        // Use the first non-quit trace
        val trace = traces.first { t ->
            t.moves.none { it.assignments.values.any { v -> v is Expr.Const.Quit } }
        }

        require(timeoutAfter < trace.moves.size) {
            "timeoutAfter=$timeoutAfter but trace only has ${trace.moves.size} moves"
        }

        val rpc = EthJsonRpc(anvil.rpcUrl)
        val ethRuntime = EthereumRuntime(rpc, anvil.accounts)
        val ethSession = ethRuntime.deploy(game) as EthereumSession

        // Play moves up to the timeout point
        for (i in 0 until timeoutAfter) {
            ethSession.submitMove(trace.moves[i])
        }

        // Advance time past timeout
        rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)

        // Try to execute remaining non-join moves that the contract may accept
        // after timeout (depends modifier sets bailed flags)
        for (i in timeoutAfter until trace.moves.size) {
            val move = trace.moves[i]
            // Skip — after timeout, the bailed role's actions are skipped by the contract
            // The depends modifier handles this: if predecessor timed out, bailed[role] = true
            try {
                ethSession.submitMove(move)
            } catch (_: TxRevertedException) {
                // Expected: some moves may revert after timeout
            }
        }

        // Verify withdrawals execute (bail-out payoffs should be valid)
        val payoffs = ethSession.executeWithdrawals()

        // Basic sanity: total payoffs should not exceed total deposits
        val totalDeposits = game.roles.sumOf {
            try { game.dag.deposit(it).v } catch (_: Exception) { 0 }
        }
        val totalPayoffs = payoffs.values.sum()
        require(totalPayoffs <= totalDeposits.toLong()) {
            "Timeout test ($gameName, after=$timeoutAfter): total payoffs $totalPayoffs > deposits $totalDeposits"
        }
    }

    // ========== Prisoners: timeout after joins ==========

    test("Prisoners: timeout after both join") {
        testTimeoutAt("Prisoners", timeoutAfter = 2) // after A join, B join
    }

    test("Prisoners: timeout after one commit") {
        testTimeoutAt("Prisoners", timeoutAfter = 3) // after joins + A commit
    }

    // ========== Simple: commit-reveal sequential ==========

    test("Simple: timeout after joins") {
        testTimeoutAt("Simple", timeoutAfter = 2)
    }

    test("Simple: timeout after A commits") {
        testTimeoutAt("Simple", timeoutAfter = 3)
    }

    // ========== Centipede: sequential with || handlers ==========

    test("Centipede: timeout after joins") {
        testTimeoutAt("Centipede", timeoutAfter = 2)
    }

    test("Centipede: timeout after first move") {
        testTimeoutAt("Centipede", timeoutAfter = 3)
    }
})

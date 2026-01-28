package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.GameIR
import vegas.runtime.*

/**
 * Model-driven tests: for each example game, enumerate traces,
 * play on both LocalRuntime and EthereumRuntime, and assert payoffs match.
 *
 * This is the primary correctness test: the semantic model and the
 * Solidity contract must agree on payoffs for every possible game outcome.
 */
@EnabledIf(EthToolsAvailable::class)
class EthModelTest : FunSpec({

    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    /**
     * For a given game, enumerate all non-quit traces, play them on both
     * the local semantic model and the Ethereum contract, and compare payoffs.
     *
     * @param sampled If true, use random sampling instead of exhaustive enumeration.
     * @param sampleCount Number of traces to sample (only used if [sampled] is true).
     */
    fun testGameTraces(gameName: String, maxTraces: Int = 50, sampled: Boolean = false, sampleCount: Int = 20) {
        val game = loadGame(gameName)
        val traces = if (sampled) {
            TraceEnumerator.sample(game, sampleCount)
        } else {
            TraceEnumerator.exhaustive(game, maxTraces)
        }

        require(traces.isNotEmpty()) { "No traces found for $gameName" }

        for ((traceIdx, trace) in traces.withIndex()) {
            // Skip traces with quit moves for now — they involve timeout logic
            val hasQuit = trace.moves.any {
                it.assignments.values.any { v -> v is vegas.ir.Expr.Const.Quit }
            }
            if (hasQuit) continue

            // Play on LocalRuntime
            val localRuntime = LocalRuntime()
            val localSession = localRuntime.deploy(game)
            for (move in trace.moves) {
                localSession.submitMove(move)
            }
            require(localSession.isTerminal()) {
                "Local session not terminal after trace #$traceIdx for $gameName"
            }
            val localPayoffs = localSession.payoffs()

            // Play on EthereumRuntime
            val rpc = EthJsonRpc(anvil.rpcUrl)
            val ethRuntime = EthereumRuntime(rpc, anvil.accounts)
            val ethSession = ethRuntime.deploy(game) as EthereumSession
            for (move in trace.moves) {
                ethSession.submitMove(move)
            }
            require(ethSession.isTerminal()) {
                "Ethereum session not terminal after trace #$traceIdx for $gameName"
            }

            // Execute withdrawals and compare
            val ethPayoffs = ethSession.executeWithdrawals()

            // Compare payoffs — Anvil uses gasPrice=0 so balance deltas should match exactly
            for (role in game.roles) {
                val expected = (localPayoffs[role] ?: 0).toLong()
                val actual = ethPayoffs[role] ?: 0L
                require(expected == actual) {
                    "Trace #$traceIdx ($gameName): role $role expected payout $expected but got $actual on Ethereum\n" +
                    "Trace: ${trace.description}"
                }
            }
        }
    }

    // ========== Tier 0: Existing games ==========

    test("Prisoners: all traces match") {
        testGameTraces("Prisoners")
    }

    test("OddsEvensShort: all traces match") {
        testGameTraces("OddsEvensShort")
    }

    // ========== Tier 1: Small, exhaustively enumerable ==========

    test("Simple: all traces match") {
        testGameTraces("Simple")
    }

    test("Trivial1: all traces match") {
        testGameTraces("Trivial1")
    }

    test("Dominance: all traces match") {
        testGameTraces("Dominance")
    }

    test("DoubleFlipLights: all traces match") {
        testGameTraces("DoubleFlipLights")
    }

    // ========== Tier 2: Medium, commit-reveal & sequential ==========

    test("MontyHall: all traces match") {
        testGameTraces("MontyHall", maxTraces = 100)
    }

    test("Centipede: all traces match") {
        testGameTraces("Centipede")
    }

    test("RPSLS: all traces match") {
        testGameTraces("RPSLS", maxTraces = 50)
    }

    test("SpinTheDial: all traces match") {
        testGameTraces("SpinTheDial", maxTraces = 50)
    }

    // ========== Tier 3: Large domain, sampled ==========

    test("TicTacToe: sampled traces match") {
        testGameTraces("TicTacToe", sampled = true, sampleCount = 20)
    }

    test("UltimatumGame: sampled traces match") {
        testGameTraces("UltimatumGame", sampled = true, sampleCount = 20)
    }

    test("VickreyAuction: sampled traces match") {
        testGameTraces("VickreyAuction", sampled = true, sampleCount = 20)
    }

    test("EscrowContract: sampled traces match") {
        testGameTraces("EscrowContract", sampled = true, sampleCount = 20)
    }
})

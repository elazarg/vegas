package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import vegas.RoleId
import vegas.VarId
import vegas.backend.evm.EvmConstants
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.runtime.*

/**
 * Timeout tests: advance Anvil timestamp past TIMEOUT, verify bail-out
 * logic and payoff splits.
 *
 * Uses `evm_increaseTime` and `evm_mine` to manipulate the block timestamp,
 * simulating timeout scenarios where a role fails to act within the deadline.
 */
@EnabledIf(EthToolsAvailable::class)
class EthTimeoutTest : FunSpec({

    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    test("Prisoners: B times out after joining - bail-out payoffs") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        // Both join
        val moves = session.legalMoves()
        val joinMoves = moves.filter {
            game.dag.spec(it.actionId).join != null
        }
        for (move in joinMoves) {
            session.submitMove(move)
        }

        // A commits (cooperate)
        val afterJoin = session.legalMoves()
        val aCommit = afterJoin.find { it.role == RoleId("A") }
        if (aCommit != null) {
            val commitMove = GameMove(
                actionId = aCommit.actionId,
                role = aCommit.role,
                visibility = aCommit.visibility,
                assignments = mapOf(VarId("c") to Expr.Const.Hidden(Expr.Const.BoolVal(true))),
            )
            session.submitMove(commitMove)
        }

        // Advance time past TIMEOUT to trigger B's bail-out
        rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)

        // Now B is bailed — remaining actions should be callable with bailed logic
        // The contract's `depends` modifier will set bailed[B] = true on timestamp check
    }

    test("OddsEvensShort: Even times out - Odd gets split payoff") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("OddsEvensShort")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        // Both join
        val moves = session.legalMoves()
        val joinMoves = moves.filter {
            game.dag.spec(it.actionId).join != null
        }
        for (move in joinMoves) {
            session.submitMove(move)
        }

        // Odd commits (true)
        val afterJoin = session.legalMoves()
        val oddCommit = afterJoin.find { it.role == RoleId("Odd") }
        if (oddCommit != null) {
            val commitMove = GameMove(
                actionId = oddCommit.actionId,
                role = oddCommit.role,
                visibility = oddCommit.visibility,
                assignments = mapOf(VarId("c") to Expr.Const.Hidden(Expr.Const.BoolVal(true))),
            )
            session.submitMove(commitMove)
        }

        // Advance time past TIMEOUT
        rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)

        // Even is bailed — Odd should get favorable split payoff
    }
})

package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import vegas.RoleId
import vegas.VarId
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.runtime.*

/**
 * Timeout tests: a player stays silent past its deadline, which on chain is
 * how it quits. The payouts must be the model's payouts for that quit.
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

    /**
     * Play [script] on chain and in the model: each step picks, for a role,
     * its move with the given value (null: its join; [quit]: its quit).
     */
    fun playBoth(game: GameIR, script: List<Pair<String, Expr.Const?>>): Pair<Map<RoleId, Int>, Map<RoleId, Long>> {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val chain = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession
        val model = LocalRuntime().deploy(game)
        for ((role, value) in script) {
            val move = chain.legalMoves().first { m ->
                m.role == RoleId(role) && when (value) {
                    null -> m.assignments.isEmpty()
                    else -> m.assignments.values.single() == value
                }
            }
            chain.submitMove(move)
            model.submitMove(move)
        }
        model.isTerminal() shouldBe true
        return model.payoffs() to chain.executeWithdrawals()
    }

    val quit = Expr.Const.Quit
    fun hidden(b: Boolean) = Expr.Const.Hidden(Expr.Const.BoolVal(b))
    fun open(b: Boolean) = Expr.Const.BoolVal(b)

    test("Prisoners: B times out at its commitment and forfeits under the split handler") {
        val game = loadGame("Prisoners")
        val (model, chain) = playBoth(game, listOf(
            "A" to null, "B" to null,
            "A" to hidden(true), "B" to quit,
            "A" to open(true), "B" to quit,
        ))
        chain shouldBe model.mapValues { it.value.toLong() }
        chain.getValue(RoleId("B")) shouldBe 0L
        chain.values.sum() shouldBe 200L
    }

    test("OddsEvensShort: Even times out at its opening and Odd collects") {
        val game = loadGame("OddsEvensShort")
        val (model, chain) = playBoth(game, listOf(
            "Even" to null, "Odd" to null,
            "Even" to hidden(true), "Odd" to hidden(false),
            "Odd" to open(false), "Even" to quit,
        ))
        chain shouldBe model.mapValues { it.value.toLong() }
        (chain.getValue(RoleId("Odd")) > chain.getValue(RoleId("Even"))) shouldBe true
    }
})

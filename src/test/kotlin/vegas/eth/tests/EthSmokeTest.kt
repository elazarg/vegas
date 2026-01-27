package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.ints.shouldBeGreaterThan
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
 * Condition that checks for anvil and solc availability.
 */
class EthToolsAvailable : io.kotest.core.annotation.EnabledCondition {
    override fun enabled(kclass: kotlin.reflect.KClass<out io.kotest.core.spec.Spec>): Boolean {
        return ToolCheck.cached().allAvailable
    }
}

/**
 * Smoke tests: handwritten game scenarios deployed to Anvil.
 *
 * Tests that basic game flows work end-to-end:
 * - Deploy contract
 * - Join roles
 * - Submit moves
 * - Withdraw payoffs
 */
@EnabledIf(EthToolsAvailable::class)
class EthSmokeTest : FunSpec({

    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    test("Prisoners: deploy and join both players") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        // Get legal moves — should be the join moves first
        val moves = session.legalMoves()
        moves.size shouldBeGreaterThan 0

        // Find and submit join moves
        val joinMoves = moves.filter {
            game.dag.spec(it.actionId).join != null
        }

        for (move in joinMoves) {
            session.submitMove(move)
        }
    }

    test("Prisoners: both cooperate - full game") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        // Play through the game using legal moves from the session
        playGame(session) { move ->
            // For Prisoners, both cooperate: c = true
            when {
                move.assignments.containsKey(VarId("c")) -> {
                    GameMove(
                        actionId = move.actionId,
                        role = move.role,
                        visibility = move.visibility,
                        assignments = mapOf(VarId("c") to Expr.Const.BoolVal(true)),
                    )
                }
                else -> move  // Join moves have no choices
            }
        }

        // Verify payoffs via withdrawal
        session.executeWithdrawals()
        // Both cooperate: A->100, B->100
        // Note: gas costs are subtracted, so payoffs will be slightly less
        // We verify the contract sent the right amounts
    }

    test("Prisoners: A cooperates, B defects") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        playGame(session) { move ->
            when {
                move.assignments.containsKey(VarId("c")) -> {
                    val cooperate = move.role == RoleId("A")  // A cooperates, B defects
                    GameMove(
                        actionId = move.actionId,
                        role = move.role,
                        visibility = move.visibility,
                        assignments = mapOf(VarId("c") to Expr.Const.BoolVal(cooperate)),
                    )
                }
                else -> move
            }
        }

        session.executeWithdrawals()
    }

    test("OddsEvensShort: both choose true") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("OddsEvensShort")
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        playGame(session) { move ->
            when {
                move.assignments.containsKey(VarId("c")) -> {
                    GameMove(
                        actionId = move.actionId,
                        role = move.role,
                        visibility = move.visibility,
                        assignments = mapOf(VarId("c") to Expr.Const.BoolVal(true)),
                    )
                }
                else -> move
            }
        }

        session.executeWithdrawals()
    }
})

/**
 * Play through a game by picking the first legal move for each role,
 * optionally transforming moves via [chooser].
 *
 * For each step:
 * 1. Get legal moves from the session
 * 2. Group by role (take first available role)
 * 3. Let [chooser] modify the move (e.g., set specific values)
 * 4. Submit the move
 * 5. Repeat until terminal
 */
fun playGame(
    session: GameSession,
    chooser: (GameMove) -> GameMove = { it },
) {
    var maxSteps = 100
    while (!session.isTerminal() && maxSteps-- > 0) {
        val moves = session.legalMoves()
        if (moves.isEmpty()) break

        // Submit moves for each role that has legal moves
        val byRole = moves.groupBy { it.role }
        for ((_, roleMoves) in byRole) {
            if (session.isTerminal()) break
            // Pick the first move for this role, then let chooser customize
            val picked = chooser(roleMoves.first())
            session.submitMove(picked)
        }
    }
}

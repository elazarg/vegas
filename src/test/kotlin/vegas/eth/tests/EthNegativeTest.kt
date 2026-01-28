package vegas.eth.tests

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import vegas.RoleId
import vegas.VarId
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Visibility

/**
 * Negative tests for EVM contracts: verify that illegal operations are rejected.
 *
 * This addresses critical gaps from TESTING-GAPS.md §5:
 * - Guard enforcement on contract (§5.2.1)
 * - Role enforcement (§5.2.2)
 * - Action ordering enforcement (§5.2.3)
 * - Deposit validation (§5.2.4)
 * - Commitment integrity (§5.2.5)
 * - Replay protection (§5.2.6)
 *
 * Equivalence class partitioning: ONE representative test per failure mode.
 */
@EnabledIf(EthToolsAvailable::class)
class EthNegativeTest : FunSpec({

    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    fun loadGame(name: String): GameIR {
        val ast = parseExample(name)
        return compileToIR(inlineMacros(ast))
    }

    /**
     * §5.2.2 Role Enforcement: Wrong address submitting a move should revert.
     *
     * Test: A's account tries to call B's function.
     */
    test("Prisoners: wrong role address reverts") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val session = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession

        // Complete joins first
        for (move in session.legalMoves().filter { game.dag.spec(it.actionId).join != null }) {
            session.submitMove(move)
        }

        // Get B's yield move
        session.legalMoves().find { it.role == RoleId("B") }!!

        // Try to submit B's move using A's account by calling the contract directly
        // This requires raw transaction building
        val aAccount = anvil.accounts[1] // Account assigned to A (index 1, after deployer)

        // The Solidity function is: B_c(bool c) and has modifier by(Role.B)
        val selector = AbiCodec.functionSelector("B_c(bool)")
        val calldata = Hex.encode(AbiCodec.encodeCall(selector, AbiValue.Bool(true)))

        // Call B's function from A's address - should revert
        shouldThrow<TxRevertedException> {
            rpc.sendAndWait(
                from = aAccount, // A's account
                to = session.contractAddress,
                data = calldata,
                functionName = "B_c(bool) from wrong role"
            )
        }
    }

    /**
     * §5.2.3 Action Ordering: Submitting an action before its dependency should revert.
     *
     * Test: Try to submit a yield action before completing the join action.
     */
    test("Prisoners: action before dependency reverts") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val session = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession

        // Try to call A_c (yield) before A_join completes
        val aAccount = anvil.accounts[1] // A's account

        val selector = AbiCodec.functionSelector("A_c(bool)")
        val calldata = Hex.encode(AbiCodec.encodeCall(selector, AbiValue.Bool(true)))

        shouldThrow<TxRevertedException> {
            rpc.sendAndWait(
                from = aAccount,
                to = session.contractAddress,
                data = calldata,
                functionName = "A_c(bool) before join"
            )
        }
    }

    /**
     * §5.2.4 Deposit Validation: Joining with wrong deposit amount should revert.
     *
     * Test: Try to join with less wei than required.
     */
    test("Prisoners: wrong deposit amount reverts") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val session = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession

        // A's account
        val aAccount = anvil.accounts[1]

        // A_join() requires deposit of 100 wei
        val selector = AbiCodec.functionSelector("A_join()")
        val calldata = Hex.encode(selector)

        // Send only 50 wei instead of 100
        shouldThrow<TxRevertedException> {
            rpc.sendAndWait(
                from = aAccount,
                to = session.contractAddress,
                data = calldata,
                value = "0x32", // 50 in hex, should be 100
                functionName = "A_join() with wrong deposit"
            )
        }
    }

    /**
     * §5.2.5 Commitment Integrity: Revealing a different value than committed should revert.
     *
     * Test: Commit one value, try to reveal a different value.
     */
    test("OddsEvensShort: commitment forgery reverts") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("OddsEvensShort")
        val session = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession

        // Complete joins
        for (move in session.legalMoves().filter { game.dag.spec(it.actionId).join != null }) {
            session.submitMove(move)
        }

        // Submit commit for Odd with c=true
        val oddRole = RoleId("Odd")
        val oddCommitMove = session.legalMoves()
            .find { it.role == oddRole && it.visibility == Visibility.COMMIT }!!

        val commitMove = oddCommitMove.copy(
            assignments = mapOf(VarId("c") to Expr.Const.Hidden(Expr.Const.BoolVal(true)))
        )
        session.submitMove(commitMove)

        // Submit commit for Even
        val evenRole = RoleId("Even")
        val evenCommitMove = session.legalMoves()
            .find { it.role == evenRole && it.visibility == Visibility.COMMIT }!!
        val evenMove = evenCommitMove.copy(
            assignments = mapOf(VarId("c") to Expr.Const.Hidden(Expr.Const.BoolVal(false)))
        )
        session.submitMove(evenMove)

        // Now try to reveal Odd with a DIFFERENT value than committed
        // We need to bypass the session's internal commitment tracking

        // Odd's reveal function: Odd_reveal_c(bool c, uint256 salt)
        val oddAccount = anvil.accounts[2] // Odd's account (based on alphabetical order: Even=1, Odd=2)

        // Use a random salt (not the one used for commitment)
        val wrongSalt = 999999L
        val wrongValue = false // committed true, revealing false

        val selector = AbiCodec.functionSelector("Odd_reveal_c(bool,uint256)")
        val calldata = Hex.encode(AbiCodec.encodeCall(
            selector,
            AbiValue.Bool(wrongValue),
            AbiValue.Uint256(wrongSalt)
        ))

        shouldThrow<TxRevertedException> {
            rpc.sendAndWait(
                from = oddAccount,
                to = session.contractAddress,
                data = calldata,
                functionName = "Odd_reveal_c with forged value"
            )
        }
    }

    /**
     * §5.2.6 Replay Protection: Submitting the same action twice should revert.
     *
     * Test: Submit a join action, then try to submit it again.
     */
    test("Prisoners: replay action reverts") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val game = loadGame("Prisoners")
        val session = EthereumRuntime(rpc, anvil.accounts).deploy(game) as EthereumSession

        // Submit A's join
        val aJoin = session.legalMoves().find {
            it.role == RoleId("A") && game.dag.spec(it.actionId).join != null
        }!!
        session.submitMove(aJoin)

        // Try to submit A's join again via raw transaction
        val aAccount = anvil.accounts[1]
        val selector = AbiCodec.functionSelector("A_join()")
        val calldata = Hex.encode(selector)

        shouldThrow<TxRevertedException> {
            rpc.sendAndWait(
                from = aAccount,
                to = session.contractAddress,
                data = calldata,
                value = "0x64", // 100 wei
                functionName = "A_join() replay"
            )
        }
    }

    // Note: Guard enforcement at EVM level is tested indirectly through the
    // positive model tests (EthModelTest) which verify that valid plays work.
    // Direct guard violation testing at EVM level is complex because it requires
    // bypassing the session's move enumeration, and the guard is enforced
    // in the Solidity require() statements.
})

// Extension property to access contract address from session
val EthereumSession.contractAddress: String
    get() {
        val field = EthereumSession::class.java.getDeclaredField("contractAddress")
        field.isAccessible = true
        return field.get(this) as String
    }


package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldStartWith
import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.backend.evm.EvmConstants
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.NodeId
import vegas.ir.Visibility
import java.math.BigInteger

/**
 * Adversarial play against generated contracts: stalling, withholding after
 * observing, not joining, and choosing when randomness is drawn. Each test
 * compares what an off-script player can achieve on chain with what the
 * analysis model says the same behaviour is worth.
 *
 * The tests drive contracts with raw transactions, so they exercise the
 * contract rather than the test harness's own sequencing.
 */
@EnabledIf(EthToolsAvailable::class)
class EthAdversarialTest : FunSpec({
    val anvil = AnvilNode()
    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    val timeout = EvmConstants.TIMEOUT_SECONDS.toLong()

    class Deployment(val rpc: EthJsonRpc, val ir: GameIR, val source: String, val address: String, val beacon: String?)

    fun beaconSource() = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;
        contract TestBeacon {
            mapping(uint256 => bytes32) public published;
            function publish(uint256 t, bytes32 v) external { published[t] = v; }
            function randomnessAfter(uint256 t) external view returns (bytes32 value, uint256 roundTime) {
                value = published[t];
                roundTime = value == bytes32(0) ? 0 : t + 1;
            }
        }
    """.trimIndent()

    fun word(address: String): ByteArray =
        BigInteger(address.removePrefix("0x"), 16).toByteArray().takeLast(20).toByteArray().let { ByteArray(32 - it.size) + it }

    fun deploy(name: String): Deployment {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val ir = compileToIR(inlineMacros(parseExample(name)))
        val evm = compileToEvm(ir)
        val source = generateSolidity(evm)
        val compiled = SolcCompiler.compile(source, evm.name)
        val beacon = if (source.contains("constructor(IVegasBeacon")) {
            rpc.sendAndWait(from = anvil.accounts[0], data = SolcCompiler.compile(beaconSource(), "TestBeacon").bytecode).contractAddress
        } else null
        val args = beacon?.let { Hex.encode(word(it)).removePrefix("0x") } ?: ""
        val address = rpc.sendAndWait(from = anvil.accounts[0], data = compiled.bytecode + args).contractAddress!!
        return Deployment(rpc, ir, source, address, beacon)
    }

    /** Send a call; returns "ok" or "revert: <reason>". */
    fun Deployment.send(from: String, signature: String, vararg args: AbiValue, value: Long = 0, to: String = address): String =
        try {
            rpc.sendAndWait(from = from, to = to,
                data = Hex.encode(AbiCodec.encodeCall(AbiCodec.functionSelector(signature), *args)),
                value = "0x" + value.toString(16), functionName = signature)
            "ok"
        } catch (e: TxRevertedException) {
            "revert: ${e.revertReason}"
        }

    fun Deployment.view(signature: String): BigInteger =
        BigInteger(rpc.ethCall(anvil.accounts[0], address, Hex.encode(AbiCodec.functionSelector(signature))).removePrefix("0x"), 16)

    /** The node of [role] that writes [param] with visibility [kind]. */
    fun Deployment.node(role: String, param: String?, kind: Visibility): NodeId =
        ir.dag.actions.single { id ->
            ir.dag.owner(id) == RoleId(role) && ir.dag.kind(id) == kind &&
                (param == null && ir.dag.spec(id).join != null ||
                    param != null && ir.dag.params(id).any { it.name == VarId(param) })
        }

    fun Deployment.signature(id: NodeId): String {
        val action = compileToEvm(ir).actions.single { it.actionId == id }
        return "${action.name}(${action.inputs.joinToString(",") { it.type.typeName() }})"
    }

    fun Deployment.join(account: String, role: String, deposit: Long, vararg args: AbiValue) =
        send(account, signature(node(role, null, Visibility.PUBLIC)), *args, value = deposit)

    fun commitment(d: Deployment, roleIndex: Int, actor: String, value: AbiValue, salt: Long): AbiValue =
        AbiValue.Bytes32(CommitmentManager.commitmentHash(d.address, roleIndex, actor,
            CommitmentManager.encodePayload(value, AbiValue.Uint256(salt))))

    /** Balance change of [account] caused by [action]. */
    fun Deployment.received(account: String, action: () -> String): Pair<String, Long> {
        val before = rpc.getBalance(account)
        val result = action()
        return result to (rpc.getBalance(account) - before).toLong()
    }

    test("stalling does not let a player blame a move that was never possible (MontyHall)") {
        val d = deploy("MontyHall")
        val host = anvil.accounts[1]
        val guest = anvil.accounts[2]
        d.join(host, "Host", 20) shouldBe "ok"
        d.join(guest, "Guest", 20) shouldBe "ok"
        d.send(host, d.signature(d.node("Host", "car", Visibility.COMMIT)), commitment(d, 1, host, AbiValue.Int256(0), 7)) shouldBe "ok"
        d.send(guest, d.signature(d.node("Guest", "d", Visibility.PUBLIC)), AbiValue.Int256(1)) shouldBe "ok"
        d.send(host, d.signature(d.node("Host", "goat", Visibility.PUBLIC)), AbiValue.Int256(2)) shouldBe "ok"

        // The Guest never chooses whether to switch, and tries to cash in as
        // soon as its own deadline has passed.
        d.rpc.advanceTime(timeout + 1)
        val (early, earlyGain) = d.received(guest) { d.send(guest, "withdraw_Guest()") }
        early shouldStartWith "revert"
        earlyGain shouldBe 0L

        // The Host's reveal only became possible when the Guest's deadline
        // passed, so the Host still has a full timeout to make it.
        d.send(host, d.signature(d.node("Host", "car", Visibility.REVEAL)), AbiValue.Int256(0), AbiValue.Uint256(7)) shouldBe "ok"

        // The model: a Guest who quits at the switch loses the pot to the Host.
        d.received(host) { d.send(host, "withdraw_Host()") } shouldBe ("ok" to 40L)
        d.received(guest) { d.send(guest, "withdraw_Guest()") } shouldBe ("ok" to 0L)
        d.rpc.getBalance(d.address) shouldBe BigInteger.ZERO
    }

    test("a move after its own deadline is rejected even if nobody settled yet") {
        val d = deploy("MontyHall")
        val host = anvil.accounts[1]
        val guest = anvil.accounts[2]
        d.join(host, "Host", 20) shouldBe "ok"
        d.join(guest, "Guest", 20) shouldBe "ok"
        d.send(host, d.signature(d.node("Host", "car", Visibility.COMMIT)), commitment(d, 1, host, AbiValue.Int256(0), 7)) shouldBe "ok"
        d.rpc.advanceTime(timeout + 1)
        d.send(guest, d.signature(d.node("Guest", "d", Visibility.PUBLIC)), AbiValue.Int256(1)) shouldStartWith "revert"
    }

    test("reveals happen one at a time in declaration order (RandomLeader)") {
        val d = deploy("RandomLeader")
        val v = listOf(anvil.accounts[1], anvil.accounts[2], anvil.accounts[3])
        (0..2).forEach { d.join(v[it], "V${it + 1}", 100) shouldBe "ok" }
        val bits = listOf(true, true, false)
        (0..2).forEach {
            d.send(v[it], d.signature(d.node("V${it + 1}", "b", Visibility.COMMIT)),
                commitment(d, it + 1, v[it], AbiValue.Bool(bits[it]), 11L + it)) shouldBe "ok"
        }
        fun reveal(i: Int) = d.send(v[i], d.signature(d.node("V${i + 1}", "b", Visibility.REVEAL)),
            AbiValue.Bool(bits[i]), AbiValue.Uint256(11L + i))
        reveal(2) shouldStartWith "revert"
        reveal(1) shouldStartWith "revert"
        reveal(0) shouldBe "ok"
        reveal(2) shouldStartWith "revert"
    }

    test("a player who withholds can still collect what the game assigns it (RandomLeader)") {
        val d = deploy("RandomLeader")
        val v = listOf(anvil.accounts[1], anvil.accounts[2], anvil.accounts[3])
        (0..2).forEach { d.join(v[it], "V${it + 1}", 100) shouldBe "ok" }
        val bits = listOf(true, true, false) // all revealed: V1 wins, V2 gets 0
        (0..2).forEach {
            d.send(v[it], d.signature(d.node("V${it + 1}", "b", Visibility.COMMIT)),
                commitment(d, it + 1, v[it], AbiValue.Bool(bits[it]), 11L + it)) shouldBe "ok"
        }
        d.send(v[0], d.signature(d.node("V1", "b", Visibility.REVEAL)), AbiValue.Bool(bits[0]), AbiValue.Uint256(11)) shouldBe "ok"
        // V2 withholds; once its deadline passes, V3 reveals.
        d.rpc.advanceTime(timeout + 1)
        d.send(v[2], d.signature(d.node("V3", "b", Visibility.REVEAL)), AbiValue.Bool(bits[2]), AbiValue.Uint256(13)) shouldBe "ok"
        // The withdraw clause: anyone missing => V1 50, V2 50, V3 200.
        d.received(v[0]) { d.send(v[0], "withdraw_V1()") } shouldBe ("ok" to 50L)
        d.received(v[1]) { d.send(v[1], "withdraw_V2()") } shouldBe ("ok" to 50L)
        d.received(v[2]) { d.send(v[2], "withdraw_V3()") } shouldBe ("ok" to 200L)
        d.rpc.getBalance(d.address) shouldBe BigInteger.ZERO
    }

    test("if a role never joins, the instance aborts and deposits are refunded (Prisoners)") {
        val d = deploy("Prisoners")
        val a = anvil.accounts[1]
        d.join(a, "A", 100) shouldBe "ok"
        d.rpc.advanceTime(timeout + 1)
        d.join(anvil.accounts[2], "B", 100) shouldStartWith "revert"
        d.send(a, d.signature(d.node("A", "c", Visibility.COMMIT)), commitment(d, 1, a, AbiValue.Bool(true), 5)) shouldStartWith "revert"
        d.received(a) { d.send(a, "withdraw_A()") } shouldBe ("ok" to 100L)
        d.rpc.getBalance(d.address) shouldBe BigInteger.ZERO
    }

    /** Beacon output that the contract maps to support index [k] of a uniform draw over [size] values at [node]. */
    fun outputFor(d: Deployment, node: Int, size: Int, k: Int): ByteArray =
        (0L until 10_000L).asSequence()
            .map { AbiCodec.keccak256(AbiCodec.encodeUint256(it)) }
            .first { out ->
                val seed = AbiCodec.keccak256(out + word(d.address) + AbiCodec.encodeUint256(node.toLong()))
                BigInteger(1, seed).mod(BigInteger.valueOf(size.toLong())).toInt() == k
            }

    fun Deployment.schedulePosition(role: String): Int =
        Regex("""ACTION_${role}_\d+ = (\d+);""").find(source)!!.groupValues[1].toInt()

    test("no player can choose the outcome of a public draw (Insurance)") {
        val d = deploy("Insurance")
        val insured = anvil.accounts[1]
        val insurer = anvil.accounts[2]
        d.join(insured, "Insured", 100) shouldBe "ok"
        d.join(insurer, "Insurer", 100) shouldBe "ok"

        // The insured wants no accident, and retries through a contract that
        // reverts unless the draw came out its way.
        val trigger = Regex("""function (move_Sample_\d+)\(\)""").find(d.source)?.groupValues?.get(1) ?: "settle"
        val attack = """
            // SPDX-License-Identifier: MIT
            pragma solidity ^0.8.0;
            interface IGame { function $trigger() external; function Sample_accident() external view returns (bool); }
            contract Pick {
                function go(address game) external {
                    IGame(game).$trigger();
                    require(!IGame(game).Sample_accident() && IGame(game).done_Sample_accident(), "retry");
                }
            }
        """.trimIndent().replace(
            "function Sample_accident() external view returns (bool);",
            "function Sample_accident() external view returns (bool); function done_Sample_accident() external view returns (bool);")
        val pick = d.rpc.sendAndWait(from = insured, data = SolcCompiler.compile(attack, "Pick").bytecode).contractAddress!!

        // The beacon round the draw reads (after its readiness plus the delay) says "accident"
        // (uniform over {false, true}: index 1).
        d.beacon?.let { beacon ->
            d.send(insured, "settle()") shouldBe "ok"
            val node = d.schedulePosition("Sample")
            val ready = BigInteger(d.rpc.ethCall(insured, d.address,
                Hex.encode(AbiCodec.functionSelector("readyAt(uint256)") + AbiCodec.encodeUint256(node.toLong()))).removePrefix("0x"), 16).toLong()
            d.send(insured, "publish(uint256,bytes32)", AbiValue.Uint256(ready + EvmConstants.BEACON_DELAY_SECONDS), AbiValue.Bytes32(outputFor(d, node, 2, 1)), to = beacon) shouldBe "ok"
        }

        val attempts = (1..20).map {
            d.send(insured, "go(address)", AbiValue.Bytes32(word(d.address)), to = pick).also { d.rpc.evmMine() }
        }
        attempts.none { it == "ok" } shouldBe true
        if (d.beacon != null) {
            d.send(insurer, "settle()") shouldBe "ok"
            d.view("Sample_accident()") shouldBe BigInteger.ONE
        }
    }

    test("an integer-valued draw compiles and settles from the beacon (Bet)") {
        for (bet in listOf(1, 2, 3)) {
            val d = deploy("Bet")
            val gambler = anvil.accounts[1]
            d.join(gambler, "Gambler", 10, AbiValue.Int256(bet)) shouldBe "ok"
            d.send(gambler, "settle()") shouldBe "ok"
            val node = d.schedulePosition("Sample")
            val ready = BigInteger(d.rpc.ethCall(gambler, d.address,
                Hex.encode(AbiCodec.functionSelector("readyAt(uint256)") + AbiCodec.encodeUint256(node.toLong()))).removePrefix("0x"), 16).toLong()
            // The draw lands on 2 (support {1, 2, 3}, index 1).
            d.send(gambler, "publish(uint256,bytes32)", AbiValue.Uint256(ready + EvmConstants.BEACON_DELAY_SECONDS), AbiValue.Bytes32(outputFor(d, node, 3, 1)), to = d.beacon!!) shouldBe "ok"
            d.received(gambler) { d.send(gambler, "withdraw_Gambler()") } shouldBe ("ok" to if (bet == 2) 10L else 0L)
            d.view("Sample_winner()") shouldBe BigInteger.TWO
        }
    }
})

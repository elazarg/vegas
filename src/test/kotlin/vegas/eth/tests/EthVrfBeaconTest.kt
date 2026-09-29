package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.backend.evm.EvmConstants
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import java.io.File
import java.math.BigInteger

/**
 * contracts/VrfBeacon.sol serves a Vegas draw from a VRF v2.5 coordinator.
 * The coordinator here is a stand-in with the same request and callback
 * interface; it fulfils with whatever word the test gives it.
 */
@EnabledIf(EthToolsAvailable::class)
class EthVrfBeaconTest : FunSpec({
    val anvil = AnvilNode()
    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    val coordinatorSource = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.37;
        struct RandomWordsRequest { bytes32 keyHash; uint256 subId; uint16 requestConfirmations; uint32 callbackGasLimit; uint32 numWords; bytes extraArgs; }
        interface IConsumer { function rawFulfillRandomWords(uint256 requestId, uint256[] calldata randomWords) external; }
        contract StandInCoordinator {
            uint256 public nextId = 1;
            mapping(uint256 => address) public consumerOf;
            bytes public lastExtraArgs;
            function requestRandomWords(RandomWordsRequest calldata req) external returns (uint256 id) {
                require(req.numWords == 1, "one word");
                id = nextId++;
                consumerOf[id] = msg.sender;
                lastExtraArgs = req.extraArgs;
            }
            function fulfil(uint256 id, uint256 word) external {
                uint256[] memory words = new uint256[](1);
                words[0] = word;
                IConsumer(consumerOf[id]).rawFulfillRandomWords(id, words);
            }
        }
    """.trimIndent()

    fun word(address: String) = AbiCodec.encodeAddress(address)
    fun call(rpc: EthJsonRpc, from: String, to: String, signature: String, vararg args: ByteArray): String = try {
        rpc.sendAndWait(from = from, to = to, data = Hex.encode(AbiCodec.functionSelector(signature) + args.fold(ByteArray(0)) { a, b -> a + b }))
        "ok"
    } catch (e: TxRevertedException) {
        "revert: ${e.revertReason}"
    }
    fun view(rpc: EthJsonRpc, to: String, signature: String, vararg args: ByteArray): BigInteger = BigInteger(
        rpc.ethCall(anvil.accounts[0], to, Hex.encode(AbiCodec.functionSelector(signature) + args.fold(ByteArray(0)) { a, b -> a + b }))
            .removePrefix("0x").take(64), 16)

    test("a Vegas draw is served by VRF, requested by anyone after readiness, fulfilled only by the coordinator") {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val deployer = anvil.accounts[0]
        val coordinator = rpc.sendAndWait(from = deployer, data = SolcCompiler.compile(coordinatorSource, "StandInCoordinator").bytecode).contractAddress!!
        val beaconBin = SolcCompiler.compile(File("contracts/VrfBeacon.sol").readText(), "VrfBeacon").bytecode
        val beacon = rpc.sendAndWait(from = deployer,
            data = beaconBin + Hex.encode(word(coordinator) + ByteArray(32) { 7 } + AbiCodec.encodeUint256(42)).removePrefix("0x")).contractAddress!!

        val evm = compileToEvm(compileToIR(inlineMacros(parseExample("Bet"))))
        val game = rpc.sendAndWait(from = deployer,
            data = SolcCompiler.compile(generateSolidity(evm), evm.name).bytecode + Hex.encode(word(beacon)).removePrefix("0x")).contractAddress!!
        val gambler = anvil.accounts[1]
        rpc.sendAndWait(from = gambler, to = game, value = "0xa",
            data = Hex.encode(AbiCodec.encodeCall(AbiCodec.functionSelector("move_Gambler_0(int256)"), AbiValue.Int256(2))))
        call(rpc, deployer, game, "settle()") shouldBe "ok"
        val node = evm.schedule.nodes.indexOfFirst { it.kind == vegas.backend.evm.EvmNodeKind.DRAW }
        val ready = view(rpc, game, "readyAt(uint256)", AbiCodec.encodeUint256(node.toLong())).toLong()

        // The draw reads the round after its readiness plus the beacon delay. That round
        // can be requested only once its time has passed; then anyone may request it, once,
        // and nobody can fulfil it in the coordinator's place.
        val round = ready + EvmConstants.BEACON_DELAY_SECONDS
        call(rpc, anvil.accounts[3], beacon, "request(uint256)", AbiCodec.encodeUint256(round)) shouldContain "too early"
        rpc.advanceTime(round - rpc.latestBlockTimestamp() + 1)
        call(rpc, anvil.accounts[3], beacon, "request(uint256)", AbiCodec.encodeUint256(round)) shouldBe "ok"
        call(rpc, anvil.accounts[3], beacon, "request(uint256)", AbiCodec.encodeUint256(round)) shouldContain "already requested"
        call(rpc, gambler, beacon, "rawFulfillRandomWords(uint256,uint256[])", AbiCodec.encodeUint256(1),
            AbiCodec.encodeUint256(64), AbiCodec.encodeUint256(1), AbiCodec.encodeUint256(5)) shouldContain "only coordinator"
        call(rpc, anvil.accounts[3], beacon, "request(uint256)", AbiCodec.encodeUint256(round + 1000)) shouldContain "too early"
        // The request carries VRF v2.5's ExtraArgsV1 tag.
        val extra = rpc.ethCall(deployer, coordinator, Hex.encode(AbiCodec.functionSelector("lastExtraArgs()"))).removePrefix("0x")
        extra.drop(128).take(8) shouldBe Hex.encode(AbiCodec.keccak256("VRF ExtraArgsV1")).removePrefix("0x").take(8)

        // Before fulfilment the draw is pending; after it, the game settles from the VRF word.
        call(rpc, deployer, game, "settle()") shouldBe "ok"
        view(rpc, game, "done_Sample_winner()") shouldBe BigInteger.ZERO
        val vrfWord = BigInteger("123456789")
        call(rpc, deployer, coordinator, "fulfil(uint256,uint256)", AbiCodec.encodeUint256(1), AbiCodec.encodeUint256(vrfWord.toLong())) shouldBe "ok"
        call(rpc, deployer, game, "settle()") shouldBe "ok"
        view(rpc, game, "done_Sample_winner()") shouldBe BigInteger.ONE
        val seed = AbiCodec.keccak256(AbiCodec.encodeUint256(vrfWord.toLong()) + word(game) + AbiCodec.encodeUint256(node.toLong()))
        val expected = listOf(1, 2, 3)[BigInteger(1, seed).mod(BigInteger.valueOf(3)).toInt()]
        view(rpc, game, "Sample_winner()") shouldBe BigInteger.valueOf(expected.toLong())
    }
})

package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import vegas.RoleId
import vegas.backend.evm.*
import vegas.backend.evm.EvmType.*
import vegas.eth.*

/**
 * Deadlines of the rendered schedule, on chain. Two independent source
 * nodes (First, Second) precede a Trigger node.
 */
@EnabledIf(EthToolsAvailable::class)
class EthScheduleDeadlineTest : FunSpec({
    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    val first = RoleId("First")
    val second = RoleId("Second")
    val trigger = RoleId("Trigger")
    val timeout = EvmConstants.TIMEOUT_SECONDS.toLong()

    val contract = EvmContract(
        name = "ScheduleDeadline",
        roles = listOf(first, second, trigger),
        storage = listOf(EvmStorageSlot("roles", Mapping(Address, EnumType("Role")))),
        enums = listOf(EvmEnum("Role", listOf("None", "First", "Second", "Trigger"))),
        events = emptyList(),
        schedule = EvmSchedule(
            nodes = listOf(
                EvmScheduleNode(first to 0, first, emptyList(), EvmNodeKind.MOVE),
                EvmScheduleNode(second to 0, second, emptyList(), EvmNodeKind.MOVE),
                EvmScheduleNode(trigger to 1, trigger, listOf(0, 1), EvmNodeKind.MOVE),
            ),
            draws = emptyList(),
        ),
        actions = emptyList(),
        withdrawals = emptyList(),
        initialization = emptyList(),
    )

    fun deploy(): Pair<EthJsonRpc, String> {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val compiled = SolcCompiler.compile(generateSolidity(contract), contract.name)
        val receipt = rpc.sendAndWait(from = anvil.accounts[0], data = compiled.bytecode)
        return rpc to requireNotNull(receipt.contractAddress)
    }

    fun EthJsonRpc.settle(address: String) = sendAndWait(
        from = anvil.accounts[0],
        to = address,
        data = Hex.encode(AbiCodec.functionSelector("settle()")),
        functionName = "settle",
    )

    fun EthJsonRpc.view(address: String, signature: String, arg: Long? = null): Long {
        val data = AbiCodec.functionSelector(signature) + (arg?.let { AbiCodec.encodeUint256(it) } ?: byteArrayOf())
        return ethCall(anvil.accounts[0], address, Hex.encode(data)).removePrefix("0x").toBigInteger(16).toLong()
    }

    test("one settlement expires every concurrent missing node at its deadline") {
        val (rpc, address) = deploy()
        val deployedAt = rpc.view(address, "deployedAt()")
        rpc.advanceTime(timeout + 1)
        rpc.settle(address)
        rpc.view(address, "quitAt(uint8)", 1) shouldBe deployedAt + timeout
        rpc.view(address, "quitAt(uint8)", 2) shouldBe deployedAt + timeout
        rpc.view(address, "resolvedAt(uint256)", 0) shouldBe deployedAt + timeout
        rpc.view(address, "resolvedAt(uint256)", 1) shouldBe deployedAt + timeout
    }

    test("a node is not blamed before it was ready for a full timeout") {
        val (rpc, address) = deploy()
        val deployedAt = rpc.view(address, "deployedAt()")
        // Long after the sources expired, Trigger has only just become ready.
        rpc.advanceTime(timeout + 1)
        rpc.settle(address)
        rpc.view(address, "readyAt(uint256)", 2) shouldBe deployedAt + timeout
        rpc.view(address, "quitAt(uint8)", 3) shouldBe 0L
        rpc.view(address, "resolvedAt(uint256)", 2) shouldBe 0L
        // Its own deadline counts from its readiness.
        rpc.advanceTime(timeout)
        rpc.settle(address)
        rpc.view(address, "quitAt(uint8)", 3) shouldBe deployedAt + 2 * timeout
    }

    test("the deadline itself is still in time") {
        val (rpc, address) = deploy()
        val deployedAt = rpc.view(address, "deployedAt()")
        rpc.setNextBlockTimestamp(deployedAt + timeout)
        rpc.settle(address)
        rpc.view(address, "quitAt(uint8)", 1) shouldBe 0L
        rpc.view(address, "resolvedAt(uint256)", 0) shouldBe 0L
        rpc.advanceTime(1)
        rpc.settle(address)
        rpc.view(address, "quitAt(uint8)", 1) shouldBe deployedAt + timeout
    }
})

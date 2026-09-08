package vegas.eth.tests

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import vegas.RoleId
import vegas.backend.evm.*
import vegas.backend.evm.EvmExpr.BuiltIn
import vegas.backend.evm.EvmExpr.Member
import vegas.backend.evm.EvmStmt.Assign
import vegas.backend.evm.EvmType.*
import vegas.eth.*
import vegas.frontend.SAMPLE_OWNER

@EnabledIf(EthToolsAvailable::class)
class EthDependencySnapshotTest : FunSpec({
    val anvil = AnvilNode()

    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    val first = RoleId("First")
    val second = RoleId("Second")
    val trigger = RoleId("Trigger")
    // The fixture declares four storage slots before the emitter's bailed mapping.
    val bailedSlot = 4L

    fun contract(dependencies: List<Pair<RoleId, Int>>) = EvmContract(
        name = "DependencySnapshot",
        roles = listOf(first, second, trigger, SAMPLE_OWNER),
        storage = listOf(
            EvmStorageSlot("lastTs", Uint256),
            EvmStorageSlot("actionDone", Mapping(EnumType("Role"), Mapping(Uint256, Bool))),
            EvmStorageSlot("actionTimestamp", Mapping(EnumType("Role"), Mapping(Uint256, Uint256))),
            EvmStorageSlot("roles", Mapping(Address, EnumType("Role"))),
        ),
        enums = listOf(EvmEnum("Role", listOf("None", "First", "Second", "Trigger", "Sample"))),
        events = emptyList(),
        actions = listOf(EvmAction(
            actionId = trigger to 0,
            name = "trigger",
            invokedBy = SAMPLE_OWNER,
            inputs = emptyList(),
            payable = false,
            dependencies = dependencies,
            isTerminal = false,
            guards = emptyList(),
            body = emptyList(),
        )),
        initialization = listOf(Assign(Member(BuiltIn.Self, "lastTs"), BuiltIn.Timestamp)),
    )

    fun deploy(evm: EvmContract): Pair<EthJsonRpc, String> {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val compiled = SolcCompiler.compile(generateSolidity(evm), evm.name)
        val receipt = rpc.sendAndWait(from = anvil.accounts[0], data = compiled.bytecode)
        return rpc to requireNotNull(receipt.contractAddress)
    }

    fun invoke(rpc: EthJsonRpc, address: String) = rpc.sendAndWait(
        from = anvil.accounts[0],
        to = address,
        data = "0x" + AbiCodec.functionSelector("trigger()").joinToString("") { "%02x".format(it) },
        functionName = "trigger",
    )

    fun mappingSlot(key: Long, slot: Long): ByteArray =
        AbiCodec.keccak256(AbiCodec.encodeUint256(key) + AbiCodec.encodeUint256(slot))

    fun publicUint(rpc: EthJsonRpc, address: String, signature: String, args: ByteArray): Long {
        val data = AbiCodec.functionSelector(signature) + args
        return rpc.ethCall(anvil.accounts[0], address,
            "0x" + data.joinToString("") { "%02x".format(it) })
            .removePrefix("0x").toLong(16)
    }

    test("one call times out two missing dependencies") {
        val (rpc, address) = deploy(contract(listOf(first to 0, second to 0)))
        rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)
        invoke(rpc, address)
        rpc.getStorageAt(address, mappingSlot(1, bailedSlot)).toLong() shouldBe 1L
        rpc.getStorageAt(address, mappingSlot(2, bailedSlot)).toLong() shouldBe 1L
        publicUint(rpc, address, "actionDone(uint8,uint256)",
            AbiCodec.encodeUint256(3) + AbiCodec.encodeUint256(0)) shouldBe 1L
        publicUint(rpc, address, "lastTs()", byteArrayOf()) shouldBe rpc.latestBlockTimestamp()
    }

    test("single missing dependency retains strict timeout boundary") {
        val (boundaryRpc, boundaryAddress) = deploy(contract(listOf(first to 0)))
        val origin = publicUint(boundaryRpc, boundaryAddress, "lastTs()", byteArrayOf())
        boundaryRpc.setNextBlockTimestamp(origin + EvmConstants.TIMEOUT_SECONDS)
        shouldThrow<TxRevertedException> { invoke(boundaryRpc, boundaryAddress) }
        boundaryRpc.latestBlockTimestamp() shouldBe origin + EvmConstants.TIMEOUT_SECONDS
        publicUint(boundaryRpc, boundaryAddress, "lastTs()", byteArrayOf()) shouldBe origin
        publicUint(boundaryRpc, boundaryAddress, "actionDone(uint8,uint256)",
            AbiCodec.encodeUint256(3) + AbiCodec.encodeUint256(0)) shouldBe 0L
        boundaryRpc.getStorageAt(boundaryAddress, mappingSlot(1, bailedSlot)).toLong() shouldBe 0L

        val (overdueRpc, overdueAddress) = deploy(contract(listOf(first to 0)))
        overdueRpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)
        invoke(overdueRpc, overdueAddress)
        overdueRpc.getStorageAt(overdueAddress, mappingSlot(1, bailedSlot)).toLong() shouldBe 1L
    }
})

package vegas.backend.evm

import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.RoleId
import vegas.backend.evm.EvmType.*

/** The rendered schedule enforces readiness-relative deadlines in both backends. */
class ScheduleGenerationTest : FunSpec({
    val first = RoleId("First")
    val trigger = RoleId("Trigger")
    val contract = EvmContract(
        name = "Schedule",
        roles = listOf(first, trigger),
        storage = listOf(EvmStorageSlot("roles", Mapping(Address, EnumType("Role")))),
        enums = listOf(EvmEnum("Role", listOf("None", "First", "Trigger"))),
        events = emptyList(),
        schedule = EvmSchedule(
            nodes = listOf(
                EvmScheduleNode(first to 0, first, emptyList(), EvmNodeKind.MOVE),
                EvmScheduleNode(trigger to 1, trigger, listOf(0), EvmNodeKind.MOVE),
            ),
            draws = emptyList(),
        ),
        actions = listOf(EvmAction(
            actionId = trigger to 1,
            node = 1,
            name = "trigger",
            invokedBy = trigger,
            inputs = emptyList(),
            payable = false,
            isJoin = false,
            guards = emptyList(),
            body = emptyList(),
        )),
        withdrawals = emptyList(),
        initialization = emptyList(),
    )

    fun String.withoutIndentation(): String = lineSequence().joinToString("\n") { it.trim() }

    test("Solidity expires a node only once it is ready, at its own deadline") {
        val solidity = generateSolidity(contract).withoutIndentation()
        solidity shouldContain """
            if (block.timestamp > ready + TIMEOUT) {
            quitAt[owner] = ready + TIMEOUT;
            resolvedAt[i] = ready + TIMEOUT;
        """.trimIndent()
        solidity shouldContain """
            function _predecessors(uint256 i) internal pure returns (uint256) {
            if (i == 0) return 0;
            return 1;
            }
        """.trimIndent()
        solidity shouldContain "_beginMove(1, Role.Trigger);"
        solidity shouldNotContain "lastTs"
    }

    test("Vyper expires a node only once it is ready, at its own deadline") {
        val vyper = generateVyper(contract).withoutIndentation()
        vyper shouldContain """
            if block.timestamp > ready + TIMEOUT:
            self.quitAt[owner] = ready + TIMEOUT
            self.resolvedAt[i] = ready + TIMEOUT
        """.trimIndent()
        vyper shouldContain "self._beginMove(1, Role.Trigger)"
        vyper shouldNotContain "lastTs"
    }
})

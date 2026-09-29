package vegas.backend.evm

import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
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

    test("an audited schedule grants events one at a time; joins stay concurrent") {
        val game = vegas.frontend.compileToIR(vegas.frontend.inlineMacros(vegas.golden.parseExample("Coordination")))
        fun predecessors(audit: AuditPolicy?) = compileToEvm(game, audit).schedule.nodes.map { it.predecessors }
        // Joins of Alice and Bob, their commitments, their openings.
        predecessors(null) shouldBe
            listOf(emptyList(), emptyList(), listOf(0, 1), listOf(0, 1), listOf(0, 1, 2, 3), listOf(0, 1, 2, 3, 4))
        // Only Bob's commitment gains a predecessor: Alice's commitment.
        predecessors(AuditPolicy()) shouldBe
            listOf(emptyList(), emptyList(), listOf(0, 1), listOf(0, 1, 2), listOf(0, 1, 2, 3), listOf(0, 1, 2, 3, 4))
    }

    test("an audited contract charges a role that lets its own commitment expire") {
        val game = vegas.frontend.compileToIR(vegas.frontend.inlineMacros(vegas.golden.parseExample("Coordination")))
        val audited = compileToEvm(game, AuditPolicy())
        audited.schedule.nodes.map { it.commitment } shouldBe listOf(false, false, true, true, false, false)
        val solidity = generateSolidity(audited).withoutIndentation()
        solidity shouldContain """
            quitAt[owner] = ready + TIMEOUT;
            if (_isCommitment(i)) _charge(owner);
        """.trimIndent()
        generateSolidity(compileToEvm(game)) shouldNotContain "_charge"
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

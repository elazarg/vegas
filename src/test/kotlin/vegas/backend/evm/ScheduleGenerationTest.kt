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

    test("an audited schedule makes events ready one at a time; joins stay concurrent") {
        val game = vegas.frontend.compileToIR(vegas.frontend.inlineMacros(vegas.golden.parseExample("Coordination")))
        fun predecessors(audit: AuditPolicy?) = compileToEvm(game, audit).schedule.nodes.map { it.predecessors }
        // Joins of Alice and Bob, their commitments, their openings.
        predecessors(null) shouldBe
            listOf(emptyList(), emptyList(), listOf(0, 1), listOf(0, 1), listOf(0, 1, 2, 3), listOf(0, 1, 2, 3, 4))
        // Only Bob's commitment gains a predecessor: Alice's commitment.
        predecessors(AuditPolicy()) shouldBe
            listOf(emptyList(), emptyList(), listOf(0, 1), listOf(0, 1, 2), listOf(0, 1, 2, 3), listOf(0, 1, 2, 3, 4))
    }

    test("an audited contract never charges quitting: an expired node only makes its owner quit") {
        val game = vegas.frontend.compileToIR(vegas.frontend.inlineMacros(vegas.golden.parseExample("Coordination")))
        val solidity = generateSolidity(compileToEvm(game, AuditPolicy())).withoutIndentation()
        solidity shouldContain """
            quitAt[owner] = ready + TIMEOUT;
            resolvedAt[i] = ready + TIMEOUT;
        """.trimIndent()
        solidity shouldNotContain "_isCommitment"
        generateSolidity(compileToEvm(game)) shouldNotContain "_charge"
    }

    test("an audited move enforces its where constraint, but a value that fails it is still a well-formed move") {
        val game = vegas.frontend.compileToIR(vegas.frontend.inlineMacros(vegas.frontend.parseCode("""
            type small = {1..3}
            game main() {
              join Alice() $ 10 Bob() $ 10;
              yield or split Alice(x: small) where Alice.x != 2;
              withdraw { Alice -> 10; Bob -> 10 }
              exit { Alice -> 0; Bob -> 0 }
            }
        """.trimIndent())))
        val audited = compileToEvm(game, AuditPolicy())
        val move = audited.actions.single { !it.isJoin }
        move.constraints.size shouldBe 1
        val solidity = generateSolidity(audited).withoutIndentation()
        fun body(signature: String) = solidity.substringAfter(signature).substringBefore("\n}\n")
        val constraint = "!= 2"
        body("function ${move.name}(") shouldContain constraint
        body("function _wellFormed_${move.name}(") shouldNotContain constraint
        // The domain check stays: a value outside the type is malformed.
        body("function _wellFormed_${move.name}(") shouldContain "<= 3"
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

package vegas.backend.evm

import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.string.shouldContain
import vegas.RoleId
import vegas.frontend.SAMPLE_OWNER

class DependencySnapshotGenerationTest : FunSpec({
    val first = RoleId("First")
    val trigger = RoleId("Trigger")
    val contract = EvmContract(
        name = "DependencySnapshot",
        roles = listOf(first, trigger, SAMPLE_OWNER),
        storage = emptyList(),
        enums = emptyList(),
        events = emptyList(),
        actions = listOf(EvmAction(
            actionId = trigger to 0,
            name = "trigger",
            invokedBy = SAMPLE_OWNER,
            inputs = emptyList(),
            payable = false,
            dependencies = listOf(first to 0),
            isTerminal = false,
            guards = emptyList(),
            body = emptyList(),
        )),
        initialization = emptyList(),
    )

    fun String.withoutIndentation(): String = lineSequence().joinToString("\n") { it.trim() }

    test("Solidity renders a call-entry dependency origin") {
        generateSolidity(contract).withoutIndentation() shouldContain """
            {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.First][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
        """.trimIndent().withoutIndentation()
    }

    test("Vyper renders a call-entry dependency origin") {
        generateVyper(contract).withoutIndentation() shouldContain """
            vegasDependencyOrigin: uint256 = self.lastTs
            if (not self.actionDone[Role.First][0]) and (block.timestamp > vegasDependencyOrigin + TIMEOUT):
        """.trimIndent().withoutIndentation()
    }
})

package vegas.golden.backends

import io.kotest.matchers.shouldBe
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.frontend.compileToIR
import vegas.golden.BackendGoldenSpec
import vegas.golden.parseExample

/**
 * Solidity backend golden master tests.
 */
class SolidityTest : BackendGoldenSpec("solidity", "sol") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateSolidity(compileToEvm(ir))
    }

    override fun sanitize(content: String): String {
        return content
            .replace(Regex("//.*\\d{10,}.*\n"), "// TIMESTAMP_COMMENT\n")
            .replace(Regex("0x[0-9a-fA-F]{40}"), "0xADDRESS")
            .replace(Regex("\\s+\n"), "\n")
            .replace(Regex("\n{3,}"), "\n\n")
            .trim()
    }

    init {
        // Backend-specific test: Solidity generation should be deterministic
        "Solidity generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = generateSolidity(compileToEvm(ir))
            val output2 = generateSolidity(compileToEvm(ir))

            sanitize(output1) shouldBe sanitize(output2)
        }
    }
}

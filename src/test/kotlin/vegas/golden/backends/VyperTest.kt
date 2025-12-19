package vegas.golden.backends

import io.kotest.matchers.shouldBe
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateVyper
import vegas.frontend.compileToIR
import vegas.golden.BackendGoldenSpec
import vegas.golden.parseExample

/**
 * Vyper backend golden master tests.
 */
class VyperTest : BackendGoldenSpec("vyper", "vy") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateVyper(compileToEvm(ir))
    }

    override fun sanitize(content: String): String {
        return content
            .replace(Regex("#.*\\d{10,}.*\n"), "# TIMESTAMP_COMMENT\n")
            .replace(Regex("0x[0-9a-fA-F]{40}"), "0xADDRESS")
            .replace(Regex("\\s+\n"), "\n")
            .replace(Regex("\n{3,}"), "\n\n")
            .trim()
    }

    init {
        // Backend-specific test: Vyper generation should be deterministic
        "Vyper generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = generateVyper(compileToEvm(ir))
            val output2 = generateVyper(compileToEvm(ir))

            sanitize(output1) shouldBe sanitize(output2)
        }
    }
}

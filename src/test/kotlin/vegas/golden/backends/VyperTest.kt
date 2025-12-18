package vegas.golden.backends

import io.kotest.matchers.shouldBe
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateVyper
import vegas.frontend.compileToIR
import vegas.golden.BackendGoldenSpec
import vegas.golden.parseExample
import vegas.golden.sanitizeOutput

/**
 * Vyper backend golden master tests.
 */
class VyperTest : BackendGoldenSpec("vyper", "vy") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateVyper(compileToEvm(ir))
    }

    init {
        // Backend-specific test: Vyper generation should be deterministic
        "Vyper generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = generateVyper(compileToEvm(ir))
            val output2 = generateVyper(compileToEvm(ir))

            sanitizeOutput(output1, "vyper") shouldBe sanitizeOutput(output2, "vyper")
        }
    }
}

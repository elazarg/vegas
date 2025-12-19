package vegas.golden.backends

import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.backend.bitcoin.generateLightningProtocol
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.golden.BackendGoldenSpec

/**
 * Lightning Network protocol backend golden master tests.
 */
class LightningTest : BackendGoldenSpec("lightning", "ln") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateLightningProtocol(ir)
    }

    override fun sanitize(content: String): String {
        return content.trim()
    }

    init {
        // Backend-specific test: Lightning generation should be deterministic
        "Lightning generation should be deterministic" {
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val program = parseCode(code).copy(name = "TestGame")
            val ir = compileToIR(program)

            val output1 = generateLightningProtocol(ir)
            val output2 = generateLightningProtocol(ir)

            sanitize(output1) shouldBe sanitize(output2)
        }

        // Backend-specific test: Lightning protocol should contain key structure
        "Lightning protocol should contain key structure" {
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val program = parseCode(code).copy(name = "TestGame")
            val ir = compileToIR(program)
            val protocol = generateLightningProtocol(ir)

            protocol shouldContain "LIGHTNING_PROTOCOL"
            protocol shouldContain "ROLES:"
            protocol shouldContain "POT:"
            protocol shouldContain "ROOT:"
            protocol shouldContain "STATES:"
            protocol shouldContain "ABORT_BALANCE:"
        }
    }
}

package vegas.golden.backends

import io.kotest.matchers.string.shouldContain
import vegas.backend.smt.generateSMT
import vegas.frontend.compileToIR
import vegas.golden.BackendGoldenSpec
import vegas.golden.parseExample

/**
 * SMT-LIB backend golden master tests.
 */
class SmtTest : BackendGoldenSpec("smt", "z3") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateSMT(ir)
    }

    init {
        // Backend-specific test: SMT generation should be valid SMT-LIB
        "SMT generation should be valid SMT-LIB" {
            val program = parseExample("Prisoners")
            val smtOutput = generateSMT(compileToIR(program))

            smtOutput shouldContain "(check-sat)"
            smtOutput shouldContain "(get-model)"
        }
    }
}

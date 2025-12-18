package vegas.golden.backends

import io.kotest.matchers.string.shouldContain
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.frontend.compileToIR
import vegas.golden.BackendGoldenSpec
import vegas.golden.parseExample

/**
 * Gambit (Extensive Form Game) backend golden master tests.
 */
class GambitTest : BackendGoldenSpec("gambit", "efg") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return generateExtensiveFormGame(ir)
    }

    init {
        // Backend-specific test: Gambit generation should preserve game structure
        "Gambit generation should preserve game structure" {
            val program = parseExample("Prisoners")
            val ir = compileToIR(program)
            val efg = generateExtensiveFormGame(ir)

            efg shouldContain "EFG 2 R"
        }
    }
}

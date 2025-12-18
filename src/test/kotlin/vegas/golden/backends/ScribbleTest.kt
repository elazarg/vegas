package vegas.golden.backends

import vegas.backend.scribble.genScribbleFromIR
import vegas.golden.BackendGoldenSpec

/**
 * Scribble protocol backend golden master tests.
 */
class ScribbleTest : BackendGoldenSpec("scribble", "scr") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return genScribbleFromIR(ir)
    }
}

package vegas.golden.backends

import vegas.golden.BackendGoldenSpec
import vegas.ir.toGraphviz

/**
 * Graphviz backend golden master tests.
 */
class GraphvizTest : BackendGoldenSpec("graphviz", "gc") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return ir.toGraphviz()
    }
}

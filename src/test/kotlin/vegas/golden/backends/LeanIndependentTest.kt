package vegas.golden.backends

import vegas.backend.gallina.LeanDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.golden.BackendGoldenSpec

/**
 * Lean 4 backend golden master tests with Independent liveness policy.
 */
class LeanIndependentTest : BackendGoldenSpec("lean-independent", "lean") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return LeanDagEncoder(ir.dag, LivenessPolicy.INDEPENDENT).generate()
    }
}

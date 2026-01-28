package vegas.golden.backends

import vegas.backend.gallina.LeanDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.golden.BackendGoldenSpec

/**
 * Lean 4 backend golden master tests with Fair Play liveness policy.
 */
class LeanFairTest : BackendGoldenSpec("lean-fair", "lean") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return LeanDagEncoder(ir.dag, LivenessPolicy.FAIR_PLAY).generate()
    }
}

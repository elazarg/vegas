package vegas.golden.backends

import vegas.backend.gallina.LeanDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.golden.BackendGoldenSpec

/**
 * Lean 4 backend golden master tests with Monotonic liveness policy.
 */
class LeanMonotoneTest : BackendGoldenSpec("lean-monotone", "lean") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return LeanDagEncoder(ir.dag, LivenessPolicy.MONOTONIC).generate()
    }
}

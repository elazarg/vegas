package vegas.golden.backends

import vegas.backend.gallina.CoqDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.golden.BackendGoldenSpec

/**
 * Gallina (Coq) backend golden master tests with Independent liveness policy.
 */
class GallinaIndependentTest : BackendGoldenSpec("gallina-independent", "v") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return CoqDagEncoder(ir.dag, LivenessPolicy.INDEPENDENT).generate()
    }
}

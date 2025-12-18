package vegas.golden.backends

import vegas.backend.gallina.CoqDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.golden.BackendGoldenSpec

/**
 * Gallina (Coq) backend golden master tests with Fair Play liveness policy.
 */
class GallinaFairTest : BackendGoldenSpec("gallina-fair", "v") {

    override fun generate(ir: vegas.ir.GameIR): String {
        return CoqDagEncoder(ir.dag, LivenessPolicy.FAIR_PLAY).generate()
    }
}

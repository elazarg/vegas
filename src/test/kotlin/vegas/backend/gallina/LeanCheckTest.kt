package vegas.backend.gallina

import io.kotest.core.annotation.Condition
import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.Spec
import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import java.io.File
import kotlin.reflect.KClass

class LeanAvailable : Condition {
    override fun evaluate(kclass: KClass<out Spec>): Boolean = LeanChecker.available
}

/** Runs `lean` on a standalone file; the output is empty exactly when it checks. */
object LeanChecker {
    val available: Boolean by lazy {
        runCatching { ProcessBuilder("lean", "--version").start().waitFor() == 0 }.getOrDefault(false)
    }

    fun check(name: String, source: String): String {
        val dir = File(System.getProperty("java.io.tmpdir"), "vegas-lean").apply { mkdirs() }
        val file = File(dir, "$name.lean").apply { writeText(source) }
        val process = ProcessBuilder("lean", file.absolutePath).redirectErrorStream(true).start()
        val output = process.inputStream.bufferedReader().readText()
        process.waitFor()
        return output.trim()
    }
}

/**
 * The Lean encodings of every example type-check, under every liveness
 * policy; and in the optional encodings, a guard discharged by a missing
 * field holds (three-valued connectives, not strict lifting).
 */
@EnabledIf(LeanAvailable::class)
class LeanCheckTest : FreeSpec({
    val examples = File("examples").listFiles { f -> f.extension == "vg" }!!.map { it.nameWithoutExtension }.sorted()

    "Lean encodings of every example check" - {
        withData(examples.flatMap { name -> LivenessPolicy.entries.map { name to it } }) { (name, policy) ->
            val ir = compileToIR(inlineMacros(parseExample(name)))
            LeanChecker.check("${name}_$policy", LeanDagEncoder(ir.dag, policy).generate()) shouldBe ""
        }
    }

    "a guard discharged by a missing field holds in the optional encodings" - {
        withData(LivenessPolicy.INDEPENDENT, LivenessPolicy.MONOTONIC) { policy ->
            val ir = compileToIR(inlineMacros(parseExample("MontyHall")))
            // The goat guard reads the Guest's door: `not defined(Guest.d) or goat != Guest.d`.
            val checks = """

                example : orOpt (lift1 (! ·) (some (Option.isSome (none : Option Int))))
                    (lift2 (fun x y => decide (x ≠ y)) (some (1 : Int)) none) = some true := rfl
                example : orOpt (lift1 (! ·) (some (Option.isSome (some (1 : Int)))))
                    (lift2 (fun x y => decide (x ≠ y)) (some (1 : Int)) (some 1)) = some false := rfl
                example : andOpt (some false) none = some false := rfl
                example : iteOpt (some true) (some (1 : Int)) none = some 1 := rfl
                example : Int.tdiv (-7) 2 = -3 ∧ Int.tmod (-7) 2 = -1 := by decide
            """.trimIndent()
            val encoding = LeanDagEncoder(ir.dag, policy).generate()
            encoding.contains("(orOpt (lift1 (! ·) (some (Option.isSome (w3.getVal (fun w => w.d_Guest)))))") shouldBe true
            LeanChecker.check("MontyHall_discharge_$policy", encoding + checks) shouldBe ""
        }
    }
})

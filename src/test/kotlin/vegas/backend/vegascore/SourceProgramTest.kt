package vegas.backend.vegascore

import io.kotest.assertions.withClue
import io.kotest.core.annotation.Condition
import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.Spec
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotBeEmpty
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.reflect.KClass

private val exampleNames =
    File("examples").listFiles { f -> f.extension == "vg" }!!.map { it.nameWithoutExtension }.sorted()

private fun elaborate(name: String): String =
    generateCoreSourceProgram(compileToIR(inlineMacros(parseExample(name))), "VegasElab.$name")

/** Examples outside the core's fragment, and why. Every other example elaborates. */
private val outsideCore = mapOf(
    "MontyHallChance" to "random role",
)

/**
 * A VegasCore checkout whose `Vegas` library is built with the installed
 * toolchain: `$VEGASCORE_DIR`, or `../VegasCore`.
 */
object VegasCore {
    val dir = File(System.getenv("VEGASCORE_DIR") ?: "../VegasCore")

    val available: Boolean by lazy {
        dir.resolve("lakefile.toml").exists() &&
            runCatching { check("Probe", CORE_PRELUDE) == "" }.getOrDefault(false)
    }

    /** Runs `lake env lean` on [source]; the output is empty exactly when it checks. */
    fun check(name: String, source: String): String {
        val tmp = File(System.getProperty("java.io.tmpdir"), "vegas-core").apply { mkdirs() }
        val file = File(tmp, "$name.lean").apply { writeText(source) }
        val process = ProcessBuilder("lake", "env", "lean", file.absolutePath)
            .directory(dir).redirectErrorStream(true).start()
        val output = process.inputStream.bufferedReader().readText()
        process.waitFor(30, TimeUnit.MINUTES)
        return output.trim()
    }
}

class VegasCoreAvailable : Condition {
    override fun evaluate(kclass: KClass<out Spec>): Boolean = VegasCore.available
}

class SourceProgramTest : FreeSpec({
    "every example elaborates, except those outside the core" {
        val refused = exampleNames.mapNotNull { name ->
            try {
                elaborate(name)
                null
            } catch (e: UnsupportedCoreElaboration) {
                name to e.message!!
            }
        }.toMap()
        refused.keys shouldBe outsideCore.keys
        for ((name, reason) in outsideCore) refused.getValue(name) shouldContain reason
    }

    "a guard Vegas checks at a reveal is declared at the author's latest commitment" {
        // `reveal Host(car) where Host.goat != Host.car`: the guard's subject is
        // goat, and it reads the Guest's published door and Host's own car.
        elaborate("MontyHall") shouldContain
            "| .here => .publication .here | (.there .here) => .commitment (.there (.there .here))"
    }

    "a private draw is a setup input" {
        elaborate("PrivateValueAuction") shouldContain
            "[(1, .privateInput .«B» (.range (1) 2)), (0, .privateInput .«A» (.range (1) 2))]"
    }
})

/** Lean checks every elaboration against VegasCore, and rejects broken ones. */
@EnabledIf(VegasCoreAvailable::class)
class SourceProgramLeanTest : FreeSpec({
    "every elaborated example checks in VegasCore" {
        val source = CORE_PRELUDE + exampleNames.filter { it !in outsideCore }.joinToString("") { "\n" + elaborate(it) }
        VegasCore.check("Elaborated", source) shouldBe ""
    }

    "VegasCore rejects a commitment that is never resolved" {
        val program = elaborate("OddsEvensShort")
        val reveal = Regex("""\n  \.reveal [^\n]*<\|""").findAll(program).last().value
        val broken = program.replace(reveal, "")
        withClue("the mutation removed a reveal") { (broken != program) shouldBe true }
        VegasCore.check("Unresolved", CORE_PRELUDE + broken).shouldNotBeEmpty()
    }

    "VegasCore rejects a guard reading another role's commitment" {
        val program = elaborate("MontyHall")
        // Host's goat guard reads the Guest's door through its publication;
        // point it at the Guest's commitment instead.
        val broken = program.replace(
            "| .here => .publication .here | (.there .here)",
            "| .here => .commitment (.there .here) | (.there .here)",
        )
        withClue("the mutation redirected the read") { (broken != program) shouldBe true }
        VegasCore.check("ForeignCommitment", CORE_PRELUDE + broken).shouldNotBeEmpty()
    }
})

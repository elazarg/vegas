package vegas.backend.vegascore

import io.kotest.assertions.throwables.shouldThrow
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
import vegas.frontend.parseCode
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.toOutcome
import vegas.semantics.eval
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.reflect.KClass

private val exampleNames =
    File("examples").listFiles { f -> f.extension == "vg" }!!.map { it.nameWithoutExtension }.sorted()

private fun exampleIR(name: String) = compileToIR(inlineMacros(parseExample(name)))

private fun elaborate(name: String): String =
    generateCoreSourceProgram(exampleIR(name), "VegasElab.$name")

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
        val log = File(tmp, "$name.log")
        val process = ProcessBuilder("lake", "env", "lean", file.absolutePath)
            .directory(dir).redirectErrorStream(true).redirectOutput(log).start()
        if (!process.waitFor(30, TimeUnit.MINUTES)) {
            process.destroyForcibly()
            return "Lean did not finish checking $name"
        }
        val output = log.readText().trim()
        return output.ifEmpty { if (process.exitValue() == 0) "" else "Lean exited with status ${process.exitValue()}" }
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

    "the emitter refuses a payout that may consume a failed number" {
        val ir = compileToIR(inlineMacros(parseCode("""
            type bid = {0..2}
            game main() {
              join Buyer() $ 2;
              yield or null Buyer(b: bid);
              withdraw { Buyer -> 2 - Buyer.b }
            }
        """.trimIndent())))
        shouldThrow<UnsupportedCoreElaboration> {
            generateCoreSourceProgram(ir, "PartialPayout")
        }.message shouldContain "possibly failed publication"
    }

    "the emitter refuses a divisor it cannot establish as nonzero" {
        val ir = compileToIR(inlineMacros(parseCode("""
            type bid = {0..2}
            game main() {
              join Buyer() $ 2;
              yield Buyer(b: bid) where 2 / Buyer.b > 0;
              withdraw { Buyer -> 2 }
            }
        """.trimIndent())))
        shouldThrow<UnsupportedCoreElaboration> {
            generateCoreSourceProgram(ir, "PartialGuard")
        }.message shouldContain "divisor is nonzero"
    }

    "a foreign failure read survives simplification of the written guard" {
        val ir = compileToIR(inlineMacros(parseCode("""
            type bid = {0..2}
            game main() {
              join Buyer() $ 2 Seller() $ 2;
              yield Buyer(b: bid);
              yield Seller(ask: bid) where alldiff(Buyer.b) && Seller.ask < 2;
              withdraw { Buyer -> 2; Seller -> 2 }
            }
        """.trimIndent())))
        val program = generateCoreSourceProgram(ir, "SimplifiedGuard")
        program.lineSequence().single { ".commit " in it && "Seller" in it } shouldContain
            "reads := fun h => match h with | .here => .publication .here"
    }

    "the emitter refuses a guard that depends on another publication failing" {
        val ir = compileToIR(inlineMacros(parseCode("""
            type bid = {0..2}
            game main() {
              join Buyer() $ 2 Seller() $ 2;
              yield or null Buyer(b: bid);
              yield Seller(confirm: bool) where Buyer.b == null;
              withdraw { Buyer -> 2; Seller -> 2 }
            }
        """.trimIndent())))
        shouldThrow<UnsupportedCoreElaboration> {
            generateCoreSourceProgram(ir, "FailureGuard")
        }.message shouldContain "tests whether another field"
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

    "the emitted guard rejects bids above the arithmetic limit" {
        val ir = compileToIR(inlineMacros(parseCode("""
            type bid = {0..2}
            game main() {
              join Buyer() $ 2;
              yield Buyer(b: bid) where Buyer.b * 2 - 1 < 3;
              withdraw { Buyer -> 2 }
            }
        """.trimIndent())))
        val program = generateCoreSourceProgram(ir, "GuardedBid")
        val guard = program.lineSequence().single { ".commit " in it }
            .substringAfter("code := ").substringBefore(", reads :=")
        val checks = """
            def bidGuard : Expr [(0, .range 0 2)] .bool := $guard
            example : evalExpr bidGuard (Env.cons (Subtype.mk 0 (by decide)) (Env.empty Val)) = true := rfl
            example : evalExpr bidGuard (Env.cons (Subtype.mk 1 (by decide)) (Env.empty Val)) = true := rfl
            example : evalExpr bidGuard (Env.cons (Subtype.mk 2 (by decide)) (Env.empty Val)) = false := rfl
        """.trimIndent()
        VegasCore.check("GuardedBid", CORE_PRELUDE + "\n" + program + "\n" + checks) shouldBe ""
    }

    "the emitted private-value auction payout agrees with the IR on every publication tuple" {
        val name = "PrivateValueAuction"
        val ir = exampleIR(name)
        val namespace = "VegasElab.$name"
        val roles = ir.roles.sortedBy { it.name }
        val cards = listOf(null, 0, 1, 2)
        val checks = buildString {
            appendLine("namespace $namespace")
            appendLine("def auctionPayouts (bidA bidB : PublicationResult (Val (.range 0 2))) : List Int :=")
            appendLine("  program.terminalPayoffs.map fun (_, payout) =>")
            appendLine("    evalExpr payout (Env.cons bidB (Env.cons bidA (Env.empty Val)))")
            for (bidA in cards) for (bidB in cards) {
                val expected = roles.map { role ->
                    val payout = ir.payoffs.getValue(role)
                    eval({ field ->
                        val bid = when (field.owner.name) {
                            "A" -> bidA
                            "B" -> bidB
                            else -> error("unexpected payout field $field")
                        }
                        bid?.let { Expr.Const.IntVal(it) } ?: Expr.Const.Quit
                    }, payout).toOutcome().v
                }
                fun result(bid: Int?): String = if (bid == null) ".failure" else "(.success (Subtype.mk $bid (by decide)))"
                appendLine("example : auctionPayouts ${result(bidA)} ${result(bidB)} = $expected := by rfl")
            }
            appendLine("end $namespace")
        }
        val specification = """
            namespace $namespace

            def settlement (bidA bidB : PublicationResult (Val (.range 0 2))) : List Int :=
              match bidA, bidB with
              | .failure, .failure => [0, 0, 4]
              | .failure, .success _ => [0, 3, 1]
              | .success _, .failure => [3, 0, 1]
              | .success a, .success b =>
                if b.val <= a.val then [2 - a.val, 2, a.val]
                else [2, 2 - b.val, b.val]

            theorem publication_cases (bid : PublicationResult (Val (.range 0 2))) :
                Or (bid = .failure) (Or (bid = .success (Subtype.mk 0 (by decide)))
                  (Or (bid = .success (Subtype.mk 1 (by decide)))
                    (bid = .success (Subtype.mk 2 (by decide))))) := by
              cases bid with
              | failure => exact Or.inl rfl
              | success value =>
                cases value with
                | mk number bounds =>
                  have lower : 0 <= number := bounds.1
                  have upper : number <= 2 := bounds.2
                  interval_cases number <;> simp

            theorem auctionPayouts_eq_settlement (bidA bidB : PublicationResult (Val (.range 0 2))) :
                auctionPayouts bidA bidB = settlement bidA bidB := by
              rcases publication_cases bidA with rfl | rfl | rfl | rfl <;>
                rcases publication_cases bidB with rfl | rfl | rfl | rfl <;> rfl

            end $namespace
        """.trimIndent()
        val source = "import Vegas.Source.Semantics\nimport Mathlib.Tactic.IntervalCases\n" +
            CORE_PRELUDE + "\n" + elaborate(name) + checks + "\n" + specification
        VegasCore.check("AuctionPayouts", source) shouldBe ""
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

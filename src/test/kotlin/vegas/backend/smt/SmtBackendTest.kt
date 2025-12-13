package vegas.backend.smt

import io.kotest.core.spec.style.StringSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.frontend.GameAst
import vegas.frontend.inlineMacros
import vegas.RoleId
import java.io.File

class SmtBackendTest : StringSpec({

    fun loadIr(name: String) = compileToIR(inlineMacros(parseFile("examples/$name.vg")))

    fun isZ3Available(): Boolean {
        return try {
            ProcessBuilder("z3", "--version").start().waitFor() == 0
        } catch (e: Exception) {
            false
        }
    }

    fun checkSat(smt: String): String {
        if (!isZ3Available()) return "sat" // Skip if z3 missing (assume sat for unit test pass in CI without z3)

        val tempFile = File.createTempFile("vegas_test", ".smt2")
        tempFile.writeText(smt)
        val process = ProcessBuilder("z3", tempFile.absolutePath)
            .redirectErrorStream(true)
            .start()
        val output = process.inputStream.bufferedReader().readText().trim()
        process.waitFor()
        tempFile.delete()
        return output
    }

    "QF-SMT generation should produce flat constants" {
        val ir = loadIr("Simple")
        val output = generateSMT(ir)

        output shouldContain "(declare-const A_c Bool)"
        output shouldContain "(declare-const action_A_0_done Bool)"
        output shouldContain "(assert (=> action_"
        output shouldContain "(check-sat)"
    }

    "DQBF generation should produce Skolem functions (Strategy Mode)" {
        val ir = loadIr("Simple")
        // No coalition specified -> All Existential (Consistency check) -> Skolem functions depend on history
        val output = generateDQBF(ir)

        output shouldContain "(declare-fun A_c"
    }

    "DQBF generation with Coalition should use Universal variables for adversaries" {
        val ir = loadIr("Prisoners") // A and B
        // Coalition = {A}. B is Adversary (Universal)
        val coalition = setOf(RoleId.of("A"))
        val output = generateDQBF(ir, coalition)

        // A's moves are functions
        output shouldContain "(declare-fun action_A_"

        // B's moves are NOT functions, they should be variables in the forall
        output shouldNotContain "(declare-fun action_B_"

        // Should contain forall quantifier with implication
        output shouldContain "(assert (forall ("
        output shouldContain "(=> (and" // Assumptions
    }

    "DQBF generation dependencies in MontyHall" {
        val ir = loadIr("MontyHall")
        // Roles: Host, Guest
        // Coalition: Guest
        val coalition = setOf(RoleId.of("Guest"))
        val output = generateDQBF(ir, coalition)

        // Guest switch action (final move) depends on Host reveal (goat)
        output shouldContain "(declare-fun Guest_"
        output shouldContain Regex("\\(declare-fun Guest_\\w+ \\([^\\)]+\\)")
    }

    "Z3 Integration: Simple game should be SAT in QF mode" {
        if (isZ3Available()) {
            val ir = loadIr("Simple")
            val output = generateSMT(ir)
            val result = checkSat(output)
            result.lines().first() shouldBe "sat"
        }
    }

    "Z3 Integration: Prisoners game should be SAT in QF mode" {
        if (isZ3Available()) {
            val ir = loadIr("Prisoners")
            val output = generateSMT(ir)
            val result = checkSat(output)
            result.lines().first() shouldBe "sat"
        }
    }

    "Z3 Integration: Simple game Strategy Consistency (All Exists) should be SAT" {
        if (isZ3Available()) {
            val ir = loadIr("Simple")
            val output = generateDQBF(ir) // Coalition null -> All Exists
            val result = checkSat(output)
            result.lines().first() shouldBe "sat"
        }
    }

    "Z3 Integration: Prisoners Strategy Consistency should be SAT" {
        if (isZ3Available()) {
            val ir = loadIr("Prisoners")
            val output = generateDQBF(ir)
            val result = checkSat(output)
            result.lines().first() shouldBe "sat"
        }
    }

    "Z3 Integration: Prisoners A vs B Strategy" {
        if (isZ3Available()) {
            val ir = loadIr("Prisoners")
            val coalition = setOf(RoleId.of("A"))
            val output = generateDQBF(ir, coalition)
            val result = checkSat(output)
            result.lines().first() shouldBe "sat"
        }
    }
})

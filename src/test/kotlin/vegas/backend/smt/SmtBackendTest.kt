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

    "QF-SMT generation should produce flat constants" {
        val ir = loadIr("Simple")
        val output = generateSMT(ir)

        // Simple.vg uses A.c (bool)
        output shouldContain "(declare-const A_c Bool)"
        output shouldContain "(declare-const action_A_0_done Bool)" // Index 0 or 2? A joins at 0. Yields at 2.
        output shouldContain "(assert (=> action_"
        output shouldContain "(check-sat)"
    }

    "DQBF generation should produce Skolem functions (Strategy Mode)" {
        val ir = loadIr("Simple")
        // No coalition specified -> All Existential (Consistency check) -> Skolem functions depend on history
        val output = generateDQBF(ir)

        // A.c is a function.
        // It depends on... A's history. A joins.
        // A.c is written in action 2 (yield A).
        // Action 2 ancestors: Action 0 (join A).
        // Action 0 writes nothing visible? (params of join).
        // So A.c might depend on nothing or just join done flag?
        // But it should be declared as a function.
        output shouldContain "(declare-fun A_c"
        // If deps empty: (declare-fun A_c () Bool)
        // If deps exist: (declare-fun A_c (Type...) Bool)
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

        // Should contain forall quantifier
        output shouldContain "(assert (forall ("
        // B's variables inside forall
        output shouldContain "(action_B_"
    }

    "DQBF generation dependencies in MontyHall" {
        val ir = loadIr("MontyHall")
        // Roles: Host, Guest
        // Coalition: Guest (we want to win)
        val coalition = setOf(RoleId.of("Guest"))
        val output = generateDQBF(ir, coalition)

        // Guest switch action (final move)
        // Depends on Host reveal (goat).
        // Host reveal writes `Host_goat`.
        // So Guest strategy for `Guest_switch` (or `Guest_door2`) should take `Host_goat` as arg.

        // Find the declaration of Guest's final move.
        // It should look like: (declare-fun Guest_switch (...) Bool)
        // And the args should include Host_goat's type (Int).

        // We can't easily parse the exact line, but we can check if there's a function with arguments.
        output shouldContain "(declare-fun Guest_"
        // Check if there is a declare-fun with at least one argument (Int or Bool)
        // Regex: \(declare-fun Guest_\w+ \([^\)]+\)
        output shouldContain Regex("\\(declare-fun Guest_\\w+ \\([^\\)]+\\)")
    }
})

package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.backend.evm.AuditPolicy
import vegas.backend.evm.auditDeposits
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.frontend.parseCode
import vegas.golden.parseExample
import vegas.semantics.UtilityBounds
import vegas.semantics.utilityBounds

/**
 * Audit deposits follow the funding hypothesis of VegasCore's
 * sequential-equilibrium theorem: coverage times deposit covers
 * `max(0, a, hi) - min(0, a, lo)`, where `lo` and `hi` bound the role's
 * utility over every way the game can end and `a` is its fixed utility after
 * quitting. An audited contract also needs the game to meet the theorem's
 * own hypotheses, and refuses one that does not.
 */
class AuditDepositTest : FreeSpec({
    fun example(name: String) = compileToIR(inlineMacros(parseExample(name)))
    fun game(code: String) = compileToIR(inlineMacros(parseCode(code)))

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")

    "bounds cover play and quits, in utility, with the exit utility separate" {
        // Coordination, net of the stake of 10: meeting is worth 6 or -6, missing -9;
        // a role whose opponent quits gets the split pot (10), and one that quits gets 0 (-10).
        utilityBounds(example("Coordination")) shouldBe mapOf(
            alice to UtilityBounds(lower = -10, upper = 10, exits = setOf(-10), intendedLower = -9),
            bob to UtilityBounds(lower = -10, upper = 10, exits = setOf(-10), intendedLower = -9),
        )
    }

    "deposits are the utility spread over coverage, rounded up" {
        val coordination = example("Coordination")
        auditDeposits(coordination, AuditPolicy()) shouldBe mapOf(alice to 20, bob to 20)
        auditDeposits(coordination, AuditPolicy(coverage = Rational(1, 4))) shouldBe mapOf(alice to 80, bob to 80)
        auditDeposits(coordination, AuditPolicy(coverage = Rational(3, 7))) shouldBe mapOf(alice to 47, bob to 47)
    }

    "a utility clause sizes the deposit, not the payout" {
        val scaled = game("""
            game main() {
              join Alice() $ 10 Bob() $ 10;
              yield or split Alice(x: bool) Bob(y: bool);
              withdraw { Alice -> 10; Bob -> 10 }
              exit { Alice -> 0; Bob -> 0 }
              utility { Alice -> Alice.payout * 3; Bob -> Bob.payout }
            }
        """.trimIndent())
        // Alice: 30 in play, 60 when Bob quits, 0 when she quits. Bob: 10, 20 and 0.
        auditDeposits(scaled, AuditPolicy()) shouldBe mapOf(alice to 60, bob to 20)
    }

    "a role that can quit needs an exit payout" {
        shouldThrow<IllegalArgumentException> { auditDeposits(example("OddsEvens"), AuditPolicy()) }
            .message!! shouldContain "exit payout"
    }

    "quitting must be no better than any outcome where nobody quits" {
        val generous = game("""
            game main() {
              join Alice() $ 10 Bob() $ 10;
              yield or split Alice(x: bool) Bob(y: bool);
              withdraw (Alice.x <-> Bob.y) ? { Alice -> 15; Bob -> 5 } : { Alice -> 5; Bob -> 15 }
              exit { Alice -> 6; Bob -> 0 }
            }
        """.trimIndent())
        shouldThrow<IllegalArgumentException> { auditDeposits(generous, AuditPolicy()) }
            .message!! shouldContain "exceeds its utility"
    }

    "the utility of a role that quit must be fixed" {
        val valued = game("""
            type worth = {1..2}
            game main() {
              join Alice() $ 10 Bob() $ 10;
              sample Alice(v: worth ~ uniform {1, 2});
              yield or split Alice(x: bool) Bob(y: bool);
              withdraw { Alice -> 10; Bob -> 10 }
              exit { Alice -> 0; Bob -> 0 }
              utility { Alice -> Alice.payout + Alice.v; Bob -> Bob.payout }
            }
        """.trimIndent())
        shouldThrow<IllegalArgumentException> { auditDeposits(valued, AuditPolicy()) }
            .message!! shouldContain "must be fixed"
    }

    "a game that cannot be enumerated is refused" {
        // Puzzle has an unbounded integer parameter.
        utilityBounds(example("Puzzle")) shouldBe null
        shouldThrow<IllegalArgumentException> { auditDeposits(example("Puzzle"), AuditPolicy()) }
            .message!! shouldContain "enumerated"
    }

    "an exit payout replaces the payout of a role that quit, in the model the backends share" {
        val ir = example("Coordination")
        ir.exits shouldBe mapOf(alice to 0, bob to 0)
        utilityBounds(ir)!!.getValue(alice).exits shouldBe setOf(-10)
    }
})

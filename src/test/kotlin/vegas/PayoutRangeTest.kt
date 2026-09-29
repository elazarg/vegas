package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import vegas.backend.evm.AuditPolicy
import vegas.backend.evm.compileToEvm
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.semantics.PayoutRange
import vegas.semantics.payoutRanges

/**
 * Bonds are sized by each role's payout range over every way the game can
 * end, including quits and an aborted instance, rather than by the pot.
 */
class PayoutRangeTest : FreeSpec({
    fun ir(name: String) = compileToIR(inlineMacros(parseExample(name)))

    "ranges cover play, quits and the refund of an aborted instance" {
        // OddsEvens: 126 / 74 when both choose, 20 / 180 when one quits, 100 each when both quit.
        payoutRanges(ir("OddsEvens")) shouldBe mapOf(
            RoleId("Odd") to PayoutRange(20, 180),
            RoleId("Even") to PayoutRange(20, 180),
        )
        // RandomLeader: V3 gets 150 in play, 200 if anyone withholds, and its 100 back if aborted.
        payoutRanges(ir("RandomLeader")) shouldBe mapOf(
            RoleId("V1") to PayoutRange(0, 150),
            RoleId("V2") to PayoutRange(0, 150),
            RoleId("V3") to PayoutRange(100, 200),
        )
    }

    "bonds are range over coverage, rounded up" {
        compileToEvm(ir("RandomLeader"), AuditPolicy()).audit!!.bonds shouldBe
            mapOf(RoleId("V1") to 150, RoleId("V2") to 150, RoleId("V3") to 100)
        compileToEvm(ir("RandomLeader"), AuditPolicy(coverage = Rational(2, 3))).audit!!.bonds shouldBe
            mapOf(RoleId("V1") to 225, RoleId("V2") to 225, RoleId("V3") to 150)
    }

    "a game that cannot be enumerated falls back to the whole pot" {
        // Puzzle has an unbounded integer parameter.
        payoutRanges(ir("Puzzle")) shouldBe null
        compileToEvm(ir("Puzzle"), AuditPolicy()).audit!!.bonds.values.toSet() shouldBe setOf(50)
    }
})

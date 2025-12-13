package vegas.backend.sui_move

import io.kotest.core.spec.style.StringSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.frontend.parseCode
import vegas.frontend.compileToIR
import vegas.backend.sui_move.compileToSuiMove
import vegas.backend.sui_move.SuiMoveRenderer

class SuiMoveBackendTest : StringSpec({
    "Compile simple game to Sui Move" {
        val code = """
            join A(x: int) $ 10;
            join B(y: int) $ 10;
            // Simple payout based on x
            withdraw (A.x > B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
        """.trimIndent()

        val program = parseCode(code).copy(name = "TestGame")
        val ir = compileToIR(program)
        val movePkg = compileToSuiMove(ir)
        val rendered = SuiMoveRenderer().render(movePkg)

        println(rendered)

        rendered shouldContain "module testgame::testgame"
        rendered shouldContain "public struct Instance<phantom Asset> has key"
        rendered shouldContain "fun join_A"
        rendered shouldContain "fun join_B"
        rendered shouldContain "fun finalize"
        rendered shouldContain "fun claim_A"
    }
})

package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.string.shouldContain
import vegas.backend.scribble.genScribbleFromIR
import vegas.frontend.compileToIR
import vegas.frontend.parseCode

class ScribbleBackendTest : FreeSpec({

    "Scribble Backend" - {
        "should generate scribble from IR" {
            val code = """
                join A(x: int);
                join B(y: hidden int);
                reveal B(y: int);
            """.trimIndent()

            val program = parseCode(code).copy(name = "TestScribble")
            val ir = compileToIR(program)
            val scribble = genScribbleFromIR(ir)

            // Basic structure checks
            scribble shouldContain "module Game;"
            scribble shouldContain "explicit global protocol TestScribble"

            // Check actions
            scribble shouldContain "Public_x(int) from A to Server"
            scribble shouldContain "Hidden_y(hidden) from B to Server"
            scribble shouldContain "Reveal_y(int) from B to Server"

            // Check broadcasts
            // A.x is Public, so it should be broadcast to B
            scribble shouldContain "Broadcast_x(int) from Server to B"
            // B.y is Revealed, so it should be broadcast to A
            scribble shouldContain "Broadcast_y(int) from Server to A"
        }
    }
})

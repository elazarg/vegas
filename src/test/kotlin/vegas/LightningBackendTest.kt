package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.string.shouldContain
import vegas.backend.bitcoin.CompilationException
import vegas.backend.bitcoin.generateLightningProtocol
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.frontend.parseCode
import java.io.File

class LightningBackendTest : FreeSpec({

    fun compileExample(filename: String, roleA: String, roleB: String, pot: Long = 1000): String {
        val file = File("examples/$filename")
        if (!file.exists()) error("Example file not found: $filename")

        val program = parseFile(file.path).copy(name = file.nameWithoutExtension)
        val ir = compileToIR(program)
        return generateLightningProtocol(ir, roleA, roleB, pot)
    }

    fun compileCode(code: String, roleA: String, roleB: String, pot: Long = 1000): String {
        val ir = compileToIR(parseCode(code))
        return generateLightningProtocol(ir, roleA, roleB, pot)
    }

    "Lightning Backend Verification" - {

        "Valid Game: SafeWTA (2-Player WTA)" {
            // Using a simple robust game to verify golden path
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val output = compileCode(code, "A", "B")
            output shouldContain "LIGHTNING_PROTOCOL"
            output shouldContain "ROLES: A=A, B=B"
            output shouldContain "ABORT_BALANCE:"
        }

        "Rejection: ThreeWayLottery.vg (3 Players)" {
            val ex = shouldThrow<CompilationException> {
                compileExample("ThreeWayLottery.vg", roleA = "Alice", roleB = "Bob")
            }
            ex.message shouldContain "requires exactly 2 strategic roles"
        }

        "Rejection: Bet.vg (1 Strategic Player)" {
            val ex = shouldThrow<CompilationException> {
                compileExample("Bet.vg", roleA = "Gambler", roleB = "Race")
            }
            ex.message shouldContain "requires exactly 2 strategic roles"
        }

        "Rejection: Chance with 2 Players (System Moves)" {
            // A game with 2 strategic players AND a random role.
            val code = """
                random Coin() $ 0;
                join Alice() $ 10;
                join Bob() $ 10;
                
                yield Coin(head: bool);
                
                withdraw (Coin.head) 
                   ? { Alice -> 20; Bob -> 0 }
                   : { Alice -> 0; Bob -> 20 }
            """.trimIndent()

            val ex = shouldThrow<CompilationException> {
                compileCode(code, "Alice", "Bob")
            }
            // Now correctly identified as unsupported system moves
            ex.message shouldContain "Unsupported system moves"
        }

        "Rejection: Non-WTA Payoffs" {
            val code = """
                join A() $ 10;
                join B() $ 10;
                withdraw { A -> 10; B -> 10 }
            """.trimIndent()

            val ex = shouldThrow<CompilationException> {
                compileCode(code, "A", "B")
            }
            ex.message shouldContain "Non-Winner-Takes-All payoff detected"
        }
    }
})

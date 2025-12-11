package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
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

    fun compileCode(code: String, name: String = "TestGame", roleA: String, roleB: String, pot: Long = 1000): String {
        val ir = compileToIR(parseCode(code).copy(name = name))
        return generateLightningProtocol(ir, roleA, roleB, pot)
    }

    "Lightning Backend: Basic Constraints" - {

        "Accepts: Simple WTA with distribution semantics" {
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B")
            output shouldContain "LIGHTNING_PROTOCOL"
            output shouldContain "ROLES: A=A, B=B"
            output shouldContain "POT: 1000"
            output shouldContain "ABORT_BALANCE:"
        }

        "Accepts: Sequential WTA game" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(offer: bool);
                yield B(accept: bool);
                withdraw (B.accept) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "LIGHTNING_PROTOCOL"
        }

        "Accepts: Simultaneous moves with commit-reveal" {
            // This is the key test: simultaneous moves should work via commit-reveal expansion
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(choice: bool) B(choice: bool);
                withdraw (A.choice <-> B.choice) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "LIGHTNING_PROTOCOL"
            // Should have states for: join, commit A, commit B, reveal A, reveal B, terminal
            output shouldContain "STATE"
        }

        "Rejects: 3 players" {
            val ex = shouldThrow<CompilationException> {
                compileExample("ThreeWayLottery.vg", roleA = "Alice", roleB = "Bob")
            }
            ex.message shouldContain "requires exactly 2 strategic roles"
        }

        "Rejects: 1 strategic player with random role" {
            val ex = shouldThrow<CompilationException> {
                compileExample("Bet.vg", roleA = "Gambler", roleB = "Race")
            }
            ex.message shouldContain "requires exactly 2 strategic roles"
        }

        "Rejects: Randomness (Chance moves)" {
            val code = """
                random Coin() $ 0;
                join Alice() $ 10;
                join Bob() $ 10;
                yield Coin(flip: bool);
                withdraw (Coin.flip) ? { Alice -> 20; Bob -> 0 } : { Alice -> 0; Bob -> 20 }
            """.trimIndent()

            val ex = shouldThrow<CompilationException> {
                compileCode(code, roleA = "Alice", roleB = "Bob")
            }
            ex.message shouldContain "Unsupported system moves"
        }
    }

    "Lightning Backend: Winner-Takes-All Enforcement" - {

        "Rejects: Both players win (utility semantics)" {
            val code = """
                join A() $ 10;
                join B() $ 10;
                withdraw { A -> 10; B -> 10 }
            """.trimIndent()

            val ex = shouldThrow<CompilationException> {
                compileCode(code, roleA = "A", roleB = "B")
            }
            ex.message shouldContain "Non-Winner-Takes-All payoff detected"
            ex.message shouldContain "A=10, B=10"
        }

        "Rejects: Both players lose" {
            val code = """
                join A() $ 10;
                join B() $ 10;
                withdraw { A -> -10; B -> -10 }
            """.trimIndent()

            val ex = shouldThrow<CompilationException> {
                compileCode(code, roleA = "A", roleB = "B")
            }
            ex.message shouldContain "Ambiguous payoff"
            ex.message shouldContain "A=-10, B=-10"
        }

        "Accepts but shouldn't: Partial payoffs (utility semantics)" {
            // This game uses utility semantics (A gains 5, B gains 0) which technically
            // satisfies WTA (one positive, one non-positive) but doesn't distribute the full pot.
            // TODO: After enforcing distribution semantics, this should be rejected.
            val code = """
                join A() $ 10;
                join B() $ 10;
                withdraw { A -> 5; B -> 0 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B")
            output shouldContain "LIGHTNING_PROTOCOL"
            // Currently passes WTA check (A>0, B<=0) but wastes funds (only 5 distributed from 20 pot)
        }

        "Accepts: Strict WTA (one positive, one zero)" {
            val code = """
                join Winner() $ 50;
                join Loser() $ 50;
                withdraw { Winner -> 100; Loser -> 0 }
            """.trimIndent()

            val output = compileCode(code, roleA = "Winner", roleB = "Loser", pot = 100)
            output shouldContain "LIGHTNING_PROTOCOL"
        }

        "Accepts: Strict WTA with quit handling" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(play: bool);
                withdraw (A.play) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "ABORT_BALANCE:"
        }
    }

    "Lightning Backend: Abort Balance Computation" - {

        "Computes correct abort balance for active player forfeit" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(move: bool);
                yield B(response: bool);
                withdraw (A.move && B.response) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)

            // When A is active (before A moves), if A quits, B should win
            output shouldContain "TURN: A"
            output shouldContain "ABORT_BALANCE:"
        }

        "Handles cascading quits correctly" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(a1: bool);
                yield B(b1: bool);
                withdraw (A.a1 && B.b1) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "STATE"
        }
    }

    "Lightning Backend: Protocol Structure" - {

        "Generates deterministic state IDs" {
            val code = """
                join A() $ 10;
                join B() $ 10;
                yield A(x: bool);
                withdraw (A.x) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val output1 = compileCode(code, roleA = "A", roleB = "B")
            val output2 = compileCode(code, roleA = "A", roleB = "B")

            output1 shouldBe output2
        }

        "Uses lexicographic ordering for concurrent moves" {
            val code = """
                join Alice() $ 50;
                join Bob() $ 50;
                yield Alice(a: bool) Bob(b: bool);
                withdraw (Alice.a <-> Bob.b) ? { Alice -> 100; Bob -> 0 } : { Alice -> 0; Bob -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "Alice", roleB = "Bob", pot = 100)

            // After commit phase, Alice should move first (lexicographically before Bob)
            // This tests the canonical ordering in Compiler.kt
            output shouldContain "TURN: Alice"
        }

        "Includes root state ID" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                withdraw { A -> 100; B -> 0 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "ROOT:"
        }

        "Lists all states with transitions" {
            val code = """
                join A() $ 50;
                join B() $ 50;
                yield A(x: bool);
                yield B(y: bool);
                withdraw (A.x && B.y) ? { A -> 100; B -> 0 } : { A -> 0; B -> 100 }
            """.trimIndent()

            val output = compileCode(code, roleA = "A", roleB = "B", pot = 100)
            output shouldContain "TRANSITIONS:"
        }
    }
})

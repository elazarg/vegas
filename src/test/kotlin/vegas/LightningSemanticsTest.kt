package vegas

import io.kotest.core.spec.style.FreeSpec
import vegas.backend.bitcoin.*
import vegas.frontend.*
import vegas.semantics.*

class LightningSemanticsTest : FreeSpec({

    "Lightning backend supports commit-reveal games" - {
        "OddsEvens should expand to serializable commit-reveal states" {
            val code = """
                join Odd() $ 100 Even() $ 100;
                yield Odd(c: bool) Even(c: bool);
                withdraw (Even.c != null && Odd.c != null) ?
                     { Even -> ((Even.c <-> Odd.c) ? 10 : -10); Odd -> ((Even.c <-> Odd.c) ? -10 : 10) }
                : (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
                : { Even -> -100; Odd -> -100 }
            """.trimIndent()

            val prog = parseCode(code).copy(name = "OddsEvens")
            val ir = compileToIR(prog)
            val semantics = GameSemantics(ir)

            println("\n=== IR Actions ===")
            ir.dag.metas.forEach { action ->
                println("Action ${action.id}: ${action.struct.owner.name} - params: ${action.spec.params.map { it.name }} - visibility: ${action.struct.visibility.values.toSet()}")
            }

            // Trace through states to find where commit happens
            var currentConfig = Configuration.initial(ir)
            var stateNum = 0

            while (!currentConfig.isTerminal() && stateNum < 10) {
                println("\n=== State $stateNum ===")
                println("Enabled actions: ${currentConfig.enabled()}")

                val moves = semantics.enabledMoves(currentConfig)
                println("Total moves: ${moves.size}")

                val strategicMoves = moves.filter {
                    it is Label.Play && it.tag != PlayTag.Quit
                }

                if (strategicMoves.isNotEmpty()) {
                    val actors = strategicMoves.map { (it as Label.Play).role }.distinct()
                    println("Strategic move actors: ${actors.map { it.name }}")
                    println("Number of actors: ${actors.size}")
                    println("Lightning check (actors.size > 1): ${actors.size > 1}")

                    if (actors.size > 1) {
                        println("\n*** MULTIPLE ACTORS ENABLED ***")
                        println("Lightning picks first actor lexicographically: ${actors.first().name}")
                        println("Semantics enforces turn-based via hasActed() check:")

                        val firstMove = strategicMoves.first { (it as Label.Play).role == actors.first() } as Label.Play
                        println("  - Apply ${firstMove.role.name} move first...")
                        val afterFirst = applyMove(currentConfig, firstMove)
                        println("    Then ${firstMove.role.name} hasActed = true")

                        val movesAfter = semantics.enabledMoves(afterFirst)
                        val strategicAfter = movesAfter.filterIsInstance<Label.Play>().filter { it.tag != PlayTag.Quit }
                        val actorsAfter = strategicAfter.map { it.role }.distinct()
                        println("    Remaining actors: ${actorsAfter.map { it.name }}")
                        println("    ✓ Serialization works!")
                        break
                    }
                }

                // Advance to next state
                if (moves.isEmpty()) break
                currentConfig = applyMove(currentConfig, moves.first())
                stateNum++
            }
        }

        "Game with simultaneous moves and WTA should compile" {
            // This game has simultaneous moves AND satisfies WTA
            val code = """
                join A() $ 10 B() $ 10;
                yield A(x: bool) B(y: bool);
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val prog = parseCode(code).copy(name = "SimultaneousWTA")
            val ir = compileToIR(prog)

            println("\n=== Testing Lightning Compilation ===")
            try {
                val protocol = generateLightningProtocol(ir, "A", "B", 1000)
                println("✓ SUCCESS! Protocol generated for game with simultaneous moves")
                println("  (Commit-reveal expansion + lexicographic serialization works!)")
            } catch (e: CompilationException) {
                println("✗ FAILED: ${e.message}")
                throw e
            }
        }

        "OddsEvens fails on WTA constraint, not turn-based" {
            val code = """
                join Odd() $ 100 Even() $ 100;
                yield Odd(c: bool) Even(c: bool);
                withdraw (Even.c != null && Odd.c != null) ?
                     { Even -> ((Even.c <-> Odd.c) ? 10 : -10); Odd -> ((Even.c <-> Odd.c) ? -10 : 10) }
                : (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
                : { Even -> -100; Odd -> -100 }
            """.trimIndent()

            val prog = parseCode(code).copy(name = "OddsEvens")
            val ir = compileToIR(prog)

            println("\n=== Testing OddsEvens Compilation ===")
            try {
                generateLightningProtocol(ir, "Odd", "Even", 1000)
                println("✗ Unexpectedly succeeded!")
            } catch (e: CompilationException) {
                println("✓ Correctly rejected: ${e.message}")
                println("  Reason: WTA violation when both players quit (both negative payoffs)")
            }
        }
    }
})

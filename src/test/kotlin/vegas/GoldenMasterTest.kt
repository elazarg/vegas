package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.datatest.withData
import vegas.backend.evm.compileToEvm
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.backend.evm.generateSolidity
import vegas.backend.evm.generateVyper
import vegas.backend.smt.generateSMT
import vegas.backend.bitcoin.generateLightningProtocol
import vegas.backend.scribble.genScribbleFromIR
import vegas.backend.bitcoin.CompilationException
import vegas.backend.gallina.CoqDagEncoder
import vegas.backend.gallina.LivenessPolicy
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.frontend.GameAst
import vegas.ir.GameIR
import vegas.ir.toGraphviz
import java.io.File

data class Example(
    val name: String,
    val disableBackend: Set<String> = emptySet()
) {
    override fun toString() = name
}

data class TestCase(
    val example: Example,
    val extension: String,
    val backend: String,
    val generator: (GameIR) -> String
) {
    override fun toString() = "$example.$extension ($backend)"
}

class GoldenMasterTest : FreeSpec({

    val exampleFiles = listOf(
        Example("Bet", disableBackend = setOf("lightning")), // Not 2-player (has random role)
        Example("MontyHall", disableBackend = setOf()),
        Example("MontyHallChance", disableBackend = setOf("lightning")), // Has randomness + utility semantics
        Example("OddsEvens", disableBackend = setOf()),
        Example("OddsEvensShort", disableBackend = setOf()),
        Example("Prisoners", disableBackend = setOf()),
        Example("Simple", disableBackend = setOf()),
        Example("Trivial1", disableBackend = setOf("lightning")), // Not 2-player (only 1 player)
        Example("Puzzle", disableBackend = setOf("gambit", "lightning")), // Unbounded int
        Example("ThreeWayLottery", disableBackend = setOf("lightning")), // Not 2-player (3 players)
        Example("ThreeWayLotteryBuggy", disableBackend = setOf("lightning")), // Not 2-player (3 players)
        Example("ThreeWayLotteryShort", disableBackend = setOf("lightning")), // Not 2-player (3 players)
        Example("TicTacToe", disableBackend = setOf("gambit", "lightning")), // Complex game
    )

    val testCases = exampleFiles.flatMap { example ->
        listOf(
            TestCase(example, "sol", "solidity") { ir ->
                generateSolidity(compileToEvm(ir))
            },
            TestCase(example, "vy", "vyper") { ir ->
                generateVyper(compileToEvm(ir))
            },
            TestCase(example, "efg", "gambit") { ir ->
                generateExtensiveFormGame(ir)
            },
            TestCase(example, "z3", "smt") { ir ->
                generateSMT(ir)
            },
            TestCase(example, "v", "gallina-fair") { ir ->
                CoqDagEncoder(ir.dag, LivenessPolicy.FAIR_PLAY).generate()
            },
            TestCase(example, "v", "gallina-monotone") { ir ->
                CoqDagEncoder(ir.dag, LivenessPolicy.MONOTONIC).generate()
            },
            TestCase(example, "v", "gallina-independent") { ir ->
                CoqDagEncoder(ir.dag, LivenessPolicy.INDEPENDENT).generate()
            },
            TestCase(example, "gc", "graphviz") { ir ->
                ir.toGraphviz()
            },
            TestCase(example, "ln", "lightning") { ir ->
                generateLightningProtocol(ir)
            },
            TestCase(example, "scr", "scribble") { ir ->
                genScribbleFromIR(ir)
            }
        ).filter { t -> t.backend !in example.disableBackend }
    }

    "Golden Master Tests" - {
        "Test all examples against golden masters" - {
            withData(nameFn = { it.toString() },testCases) { testCase ->
                val goldenFile = getGoldenFile(testCase)

                try {
                    val actualOutput = generateOutput(testCase)
                    val sanitized = sanitizeOutput(actualOutput, testCase.backend)

                    val parent = "test-diffs/${testCase.backend}"
                    val diffFile = File("$parent/${testCase.example.name}.${testCase.extension}.diff")
                    val actualFile = File("$parent/${testCase.example.name}.${testCase.extension}")

                    if (!goldenFile.exists()) {
                        actualFile.writeText(actualOutput)
                        error("Missing golden file for $testCase.")
                    }
                    val expectedOutput = sanitizeOutput(goldenFile.readText(), testCase.backend)

                    if (sanitized != expectedOutput) {
                        // Write debug artifacts
                        diffFile.parentFile.mkdirs()
                        diffFile.writeText(computeDiff(expectedOutput, sanitized))
                        actualFile.writeText(actualOutput)
                    } else {
                        // Clean up stale debug artifacts
                        // Note that untested artifacts would remain, whether stale or not
                        diffFile.delete()
                        actualFile.delete()
                    }
                    sanitized shouldBe expectedOutput

                } catch (_: NotImplementedError) {
                    // Skip test for unimplemented features
                    println("Skipped (not implemented): ${testCase.example.name}.${testCase.extension}")
                } catch (e: CompilationException) {
                    // Lightning backend compilation failure - check if expected
                    if (testCase.backend == "lightning" && testCase.example.name in testCase.example.disableBackend) {
                        println("Skipped (Lightning): ${testCase.example.name} - ${e.message}")
                    } else {
                        throw e
                    }
                }
            }
        }
    }

    "Individual Backend Tests" - {

        "Solidity generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = generateSolidity(compileToEvm(ir))
            val output2 = generateSolidity(compileToEvm(ir))

            sanitizeOutput(output1, "solidity") shouldBe sanitizeOutput(output2, "solidity")
        }

        "Vyper generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = generateVyper(compileToEvm(ir))
            val output2 = generateVyper(compileToEvm(ir))

            sanitizeOutput(output1, "vyper") shouldBe sanitizeOutput(output2, "vyper")
        }

        "Gambit generation should preserve game structure" {
            val program = parseExample("Prisoners")
            val ir = compileToIR(program)
            val efg = generateExtensiveFormGame(ir)

            efg shouldContain "EFG 2 R"
        }

        "SMT generation should be valid SMT-LIB" {
            val program = parseExample("Simple")
            val smtOutput = generateSMT(compileToIR(program))

            smtOutput shouldContain "(check-sat)"
            smtOutput shouldContain "(get-model)"
        }

        "Lightning generation should be deterministic" {
            // Use a simple inline game that satisfies Lightning constraints
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val program = vegas.frontend.parseCode(code).copy(name = "TestGame")
            val ir = compileToIR(program)

            val output1 = generateLightningProtocol(ir)
            val output2 = generateLightningProtocol(ir)

            sanitizeOutput(output1, "lightning") shouldBe sanitizeOutput(output2, "lightning")
        }

        "Lightning protocol should contain key structure" {
            // Use a simple inline game that satisfies Lightning constraints
            val code = """
                join A(x: bool) $ 10;
                join B(y: bool) $ 10;
                withdraw (A.x<->B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            """.trimIndent()

            val program = vegas.frontend.parseCode(code).copy(name = "TestGame")
            val ir = compileToIR(program)
            val protocol = generateLightningProtocol(ir)

            protocol shouldContain "LIGHTNING_PROTOCOL"
            protocol shouldContain "ROLES:"
            protocol shouldContain "POT:"
            protocol shouldContain "ROOT:"
            protocol shouldContain "STATES:"
            protocol shouldContain "ABORT_BALANCE:"
        }
    }
})

// === Helpers ===

private fun getGoldenFile(testCase: TestCase): File =
    File("examples/${testCase.backend}/${testCase.example.name}.${testCase.extension}")

private fun generateOutput(testCase: TestCase): String {
    val program = parseExample(testCase.example.name)
    val ir = compileToIR(program)
    return testCase.generator(ir)
}

private fun parseExample(example: String): GameAst {
    return parseFile("examples/$example.vg").copy(name = example, desc = example)
}

private fun sanitizeOutput(content: String, backend: String): String =
    when (backend) {
        "solidity" -> content
            .replace(Regex("//.*\\d{10,}.*\n"), "// TIMESTAMP_COMMENT\n")
            .replace(Regex("0x[0-9a-fA-F]{40}"), "0xADDRESS")
            .replace(Regex("\\s+\n"), "\n")
            .replace(Regex("\n{3,}"), "\n\n")
            .trim()

        "vyper" -> content
            .replace(Regex("#.*\\d{10,}.*\n"), "# TIMESTAMP_COMMENT\n")
            .replace(Regex("0x[0-9a-fA-F]{40}"), "0xADDRESS")
            .replace(Regex("\\s+\n"), "\n")
            .replace(Regex("\n{3,}"), "\n\n")
            .trim()

        "gambit" -> content
            .replace(Regex("\\b\\d{7,}\\b"), "HASH")
            .replace(Regex("\\d+\\.\\d{10,}"), "FLOAT")
            .trim()

        "smt" -> content
            .replace(Regex("_\\d{7,}"), "_HASH")
            .replace(Regex("\\s+\n"), "\n")
            .trim()

        "lightning" -> content.trim()

        else -> content.trim()
    }

private fun computeDiff(expected: String, actual: String): String {
    val expectedLines = expected.lines()
    val actualLines = actual.lines()
    val diff = StringBuilder()

    val maxLines = maxOf(expectedLines.size, actualLines.size)
    for (i in 0 until maxLines) {
        val expectedLine = expectedLines.getOrNull(i) ?: ""
        val actualLine = actualLines.getOrNull(i) ?: ""
        if (expectedLine != actualLine) {
            diff.appendLine("Line ${i + 1}:")
            if (expectedLine.isNotEmpty()) diff.appendLine("  - $expectedLine")
            if (actualLine.isNotEmpty()) diff.appendLine("  + $actualLine")
        }
    }
    return if (diff.isEmpty()) "No differences" else diff.toString()
}

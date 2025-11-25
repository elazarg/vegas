package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.datatest.withData
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.backend.solidity.genSolidity
import vegas.backend.smt.generateSMT
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.frontend.GameAst
import java.io.File

data class Example(
    val name: String,
    val disableBackend: Set<String> = emptySet(),
)

data class TestCase(
    val example: Example,
    val extension: String,
    val backend: String,
    val generator: (GameAst) -> String
) {
    override fun toString() = "$example.$extension ($backend)"
}

class GoldenMasterTest : FreeSpec({

    val exampleFiles = listOf(
        Example("Bet"),
        Example("MontyHall"),
        Example("MontyHallChance"),
        Example("OddsEvens"),
        Example("OddsEvensShort"),
        Example("Prisoners"),
        Example("Simple"),
        Example("Trivial1"),
        Example("Puzzle", disableBackend=setOf("gambit")),  // IntType enumeration not supported in Gambit
        Example("ThreeWayLottery"),
        Example("ThreeWayLotteryBuggy"),
        Example("ThreeWayLotteryShort"),
        Example("TicTacToe", disableBackend=setOf("gambit")),  // complex game with large state space
    )

    val testCases = exampleFiles.flatMap { example ->
        listOf(
            TestCase(example, "sol", "solidity") { prog ->
                genSolidity(compileToIR(prog))
            },
            TestCase(example, "efg", "gambit") { prog ->
                generateExtensiveFormGame(compileToIR(prog))
            },
            TestCase(example, "z3", "smt") { prog ->
                generateSMT(compileToIR(prog))
            }
        ).filter { t -> t.backend !in example.disableBackend }
    }

    "Golden Master Tests" - {
        "Test all examples against golden masters" - {
            withData(testCases) { testCase ->
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
                }
            }
        }
    }

    "Individual Backend Tests" - {

        "Solidity generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)
            val ir = compileToIR(program)

            val output1 = genSolidity(ir)
            val output2 = genSolidity(ir)

            sanitizeOutput(output1, "solidity") shouldBe sanitizeOutput(output2, "solidity")
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
    }
})

// === Helpers ===

private fun getGoldenFile(testCase: TestCase): File =
    File("examples/${testCase.backend}/${testCase.example.name}.${testCase.extension}")

private fun generateOutput(testCase: TestCase): String {
    val program = parseExample(testCase.example.name)
    return testCase.generator(program)
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

        "gambit" -> content
            .replace(Regex("\\b\\d{7,}\\b"), "HASH")
            .replace(Regex("\\d+\\.\\d{10,}"), "FLOAT")
            .trim()

        "smt" -> content
            .replace(Regex("_\\d{7,}"), "_HASH")
            .replace(Regex("\\s+\n"), "\n")
            .trim()

        else -> content.trim()
    }

private fun computeDiff(expected: String, actual: String): String {
    val expectedLines = expected.lines()
    val actualLines = actual.lines()
    val diff = StringBuilder()

    val maxLines = maxOf(expectedLines.size, actualLines.size)
    for (i in 0 until maxLines) {
        val e = expectedLines.getOrNull(i) ?: ""
        val a = actualLines.getOrNull(i) ?: ""
        if (e != a) {
            diff.appendLine("Line ${i + 1}:")
            if (e.isNotEmpty()) diff.appendLine("  - $e")
            if (a.isNotEmpty()) diff.appendLine("  + $a")
        }
    }
    return if (diff.isEmpty()) "No differences" else diff.toString()
}

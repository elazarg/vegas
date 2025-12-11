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
import vegas.backend.bitcoin.CompilationException
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.frontend.GameAst
import vegas.ir.toGraphviz
import java.io.File

data class Example(
    val name: String,
    val disableBackend: Set<String> = emptySet(),
    val disableReasons: Map<String, String> = emptyMap()
) {
    override fun toString() = name
}

data class LightningConfig(
    val roleA: String,
    val roleB: String,
    val pot: Long = 1000
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
        Example("Bet",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not 2-player (has random role)")),
        Example("MontyHall",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not winner-takes-all (Host=0 when Guest wins/loses)")),
        Example("MontyHallChance",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "has randomness (random Host role)")),
        Example("OddsEvens",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not winner-takes-all (both negative on double-quit)")),
        Example("OddsEvensShort",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not winner-takes-all (both negative on double-quit)")),
        Example("Prisoners",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not winner-takes-all (both negative when cooperate/defect)")),
        Example("Simple",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not winner-takes-all (both positive on dual quit)")),
        Example("Trivial1",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not 2-player (only 1 player)")),
        Example("Puzzle",
            disableBackend = setOf("gambit", "lightning"),
            disableReasons = mapOf(
                "lightning" to "not winner-takes-all (both players positive payoff)"
            )),
        Example("ThreeWayLottery",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not 2-player (3 players)")),
        Example("ThreeWayLotteryBuggy",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not 2-player (3 players)")),
        Example("ThreeWayLotteryShort",
            disableBackend = setOf("lightning"),
            disableReasons = mapOf("lightning" to "not 2-player (3 players)")),
        Example("TicTacToe",
            disableBackend = setOf("gambit", "lightning"),
            disableReasons = mapOf(
                "gambit" to "complex game with large state space",
                "lightning" to "not winner-takes-all (tie payoffs)"
            )),
    )

    // Lightning-specific configurations: role names and pot amount
    //
    // The Lightning backend has strict constraints that most games don't satisfy:
    // 1. Exactly 2 strategic players (no random roles, no 1 or 3+ players)
    // 2. Serializable execution (simultaneous moves are supported via commit-reveal expansion)
    // 3. Winner-Takes-All payoffs (exactly one positive winner per terminal state)
    // 4. Deterministic abort (explicit Quit moves that resolve deterministically)
    // 5. No randomness (no Chance moves or random roles)
    //
    // Currently no games in the standard test suite satisfy all these constraints:
    // - Bet, MontyHallChance, Trivial1: Not 2-player or has random roles
    // - OddsEvens, OddsEvensShort, Prisoners: Not strictly WTA (both negative payoffs in some outcomes)
    // - MontyHall, Simple, Puzzle: Not strictly WTA (zero or both-negative payoffs)
    // - ThreeWayLottery*: 3 players
    // - TicTacToe: Tie payoffs violate WTA
    //
    // Note: Simultaneous moves ARE supported (via commit-reveal + lexicographic serialization).
    // The blocker is WTA, not turn-based execution.
    //
    // Individual backend tests use inline code that satisfies all constraints.
    val lightningConfigs = mapOf<String, LightningConfig>()

    val testCases = exampleFiles.flatMap { example ->
        listOf(
            TestCase(example, "sol", "solidity") { prog ->
                generateSolidity(compileToEvm(compileToIR(prog)))
            },
            TestCase(example, "vy", "vyper") { prog ->
                generateVyper(compileToEvm(compileToIR(prog)))
            },
            TestCase(example, "efg", "gambit") { prog ->
                generateExtensiveFormGame(compileToIR(prog))
            },
            TestCase(example, "z3", "smt") { prog ->
                generateSMT(compileToIR(prog))
            },
            TestCase(example, "gc", "graphviz") { prog ->
                compileToIR(prog).toGraphviz()
            },
            TestCase(example, "ln", "lightning") { prog ->
                val config = lightningConfigs[example.name]
                    ?: throw CompilationException("Lightning backend requires role configuration for ${example.name}. " +
                        "Reason: ${example.disableReasons["lightning"] ?: "unknown"}")
                generateLightningProtocol(compileToIR(prog), config.roleA, config.roleB, config.pot)
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
                    if (testCase.backend == "lightning" && testCase.example.disableReasons.containsKey("lightning")) {
                        println("Skipped (expected exclusion): ${testCase.example.name}.${testCase.extension} - ${e.message}")
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

            val output1 = generateLightningProtocol(ir, "A", "B", 1000)
            val output2 = generateLightningProtocol(ir, "A", "B", 1000)

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
            val protocol = generateLightningProtocol(ir, "A", "B", 1000)

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

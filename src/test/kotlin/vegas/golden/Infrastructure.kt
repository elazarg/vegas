package vegas.golden

import vegas.frontend.GameAst
import vegas.frontend.parseFile
import java.io.File

/**
 * Represents a game example to be tested with golden masters.
 */
data class GameExample(
    val name: String,
    val disabledBackends: Set<String> = emptySet()
) {
    override fun toString() = name
}

/**
 * Configuration for the Golden Master tests.
 */
object GoldenMasterConfig {
    /**
     * The reduced list of non-redundant games for golden master testing.
     */
    val games = listOf(
        GameExample("MontyHall"),
        GameExample("OddsEvensShort"),
        GameExample("Prisoners"),
        GameExample("TicTacToe", disabledBackends = setOf("gambit", "lightning"))
    )

    /**
     * Returns the golden file for a given backend, game name, and extension.
     */
    fun getGoldenFile(backend: String, gameName: String, extension: String): File =
        File("src/test/resources/golden-masters/$backend/$gameName.$extension")
}

// === Helper Functions ===

/**
 * Parses a game example from the examples directory.
 */
fun parseExample(exampleName: String): GameAst {
    return parseFile("examples/$exampleName.vg")
        .copy(name = exampleName, desc = exampleName)
}

/**
 * Computes a line-by-line diff between expected and actual output.
 */
fun computeDiff(expected: String, actual: String): String {
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

/**
 * Sanitizes output for a specific backend to normalize non-deterministic elements.
 */
fun sanitizeOutput(content: String, backend: String): String =
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

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
        GameExample("TicTacToe", disabledBackends = setOf("gambit", "lightning")),
        GameExample("VickreyAuction", disabledBackends = setOf("gambit", "lightning"))
    )

    /**
     * Returns the golden file for a given backend, game name, and extension.
     */
    fun getGoldenFile(backend: String, gameName: String, extension: String): File =
        File("src/test/resources/golden-masters/$backend/$gameName.$extension")
}

// === Helper Functions ===

/**
 * Parses a game example from the examples/ directory.
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

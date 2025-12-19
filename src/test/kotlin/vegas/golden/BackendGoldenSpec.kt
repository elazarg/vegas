package vegas.golden

import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import io.kotest.matchers.shouldBe
import vegas.backend.bitcoin.CompilationException
import vegas.frontend.compileToIR
import vegas.ir.GameIR
import java.io.File

/**
 * Abstract base class for backend golden master tests.
 *
 * Each backend extends this class and implements the [generate] and [sanitize] methods.
 * The base class handles:
 * - Filtering games based on disabled backends
 * - Running parametrized tests for all applicable games
 * - Comparing generated output with golden master files
 * - Writing debug artifacts (diffs, actual outputs) when tests fail
 */
abstract class BackendGoldenSpec(
    private val backendId: String,
    private val extension: String
) : FreeSpec() {

    /**
     * Implement this to generate the specific backend code from the IR.
     */
    abstract fun generate(ir: GameIR): String

    /**
     * Implement this to sanitize generated output for comparison.
     * This normalizes non-deterministic elements (timestamps, hashes, etc.)
     * to ensure consistent test results.
     */
    protected open fun sanitize(content: String): String = content.trim()

    init {
        "Golden Masters: $backendId" - {
            // Filter games that are disabled for this backend
            val applicableGames = GoldenMasterConfig.games.filter { game ->
                backendId !in game.disabledBackends
            }

            withData(
                nameFn = { "${it.name}.$extension" },
                applicableGames
            ) { game ->
                val goldenFile = GoldenMasterConfig.getGoldenFile(backendId, game.name, extension)

                try {
                    // Parse the game and generate output
                    val ast = parseExample(game.name)
                    val ir = compileToIR(ast)
                    val actualOutput = generate(ir)
                    val sanitized = sanitize(actualOutput)

                    // Prepare debug artifact locations
                    val parent = "test-diffs/$backendId"
                    val diffFile = File("$parent/${game.name}.$extension.diff")
                    val actualFile = File("$parent/${game.name}.$extension")

                    // Check if golden file exists
                    if (!goldenFile.exists()) {
                        actualFile.parentFile?.mkdirs()
                        actualFile.writeText(actualOutput)
                        error("Missing golden file for ${game.name}.$extension")
                    }

                    // Read and sanitize expected output
                    val expectedOutput = sanitize(goldenFile.readText())

                    // Write debug artifacts if outputs differ
                    if (sanitized != expectedOutput) {
                        diffFile.parentFile.mkdirs()
                        diffFile.writeText(computeDiff(expectedOutput, sanitized))
                        actualFile.writeText(actualOutput)
                    } else {
                        // Clean up stale debug artifacts
                        diffFile.delete()
                        actualFile.delete()
                    }

                    // Assert equality
                    sanitized shouldBe expectedOutput

                } catch (_: NotImplementedError) {
                    // Skip test for unimplemented features
                    println("Skipped (not implemented): ${game.name}.$extension")
                } catch (e: CompilationException) {
                    // Lightning backend compilation failure - check if expected
                    if (backendId == "lightning" && backendId in game.disabledBackends) {
                        println("Skipped (Lightning): ${game.name} - ${e.message}")
                    } else {
                        throw e
                    }
                }
            }
        }
    }
}

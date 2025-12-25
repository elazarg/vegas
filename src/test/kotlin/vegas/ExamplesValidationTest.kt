package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import vegas.frontend.parseFile
import vegas.frontend.inlineMacros
import java.io.File

/**
 * Validates that all example .vg files parse and typecheck successfully.
 */
class ExamplesValidationTest : FreeSpec({

    val examplesDir = File("examples")

    // Find all .vg files, excluding Invalid_* files (those are expected to fail)
    val exampleFiles = examplesDir.listFiles { file ->
        file.extension == "vg" && !file.nameWithoutExtension.startsWith("Invalid_")
    }?.sorted() ?: emptyList()

    // Examples excluded due to known language design limitations (not bugs in transformation)
    val knownLanguageLimitations = setOf(
        // MontyHallChance: Demonstrates the declaration/definition split for hidden values.
        // The constraint "Host.goat != Host.car" belongs logically at the declaration site
        // (where Host.car is yielded as hidden), but can only be verified server-side at
        // the reveal site. Current language syntax doesn't support deferred constraints
        // (e.g., "where reveal Host.car != Host.goat").
        "MontyHallChance"
    )

    val examples = exampleFiles
        .map { it.nameWithoutExtension }
        .filter { it !in knownLanguageLimitations }

    "All examples should parse successfully" - {
        withData(examples) { exampleName ->
            // This will throw if parsing fails
            parseFile("examples/$exampleName.vg")
        }
    }

    "All examples should typecheck successfully" - {
        withData(examples) { exampleName ->
            val ast = try {
                parseFile("examples/$exampleName.vg")
            } catch (e: Exception) {
                throw AssertionError("Failed to parse $exampleName.vg", e)
            }

            // Type check the surface syntax (with macros)
            try {
                typeCheck(ast)
            } catch (e: Exception) {
                throw AssertionError("Failed to typecheck $exampleName.vg", e)
            }

            // Also verify macro inlining works
            try {
                inlineMacros(ast)
            } catch (e: Exception) {
                throw AssertionError("Failed to inline macros in $exampleName.vg", e)
            }
        }
    }

    "Invalid examples should fail as expected" - {
        val invalidFiles = examplesDir.listFiles { file ->
            file.extension == "vg" && file.nameWithoutExtension.startsWith("Invalid_")
        }?.sorted() ?: emptyList()

        val invalidExamples = invalidFiles.map { it.nameWithoutExtension }

        withData(invalidExamples) { exampleName ->
            val ast = parseFile("examples/$exampleName.vg")

            // Should throw StaticError or similar
            try {
                typeCheck(ast)
                throw AssertionError("Expected $exampleName to fail type checking, but it passed")
            } catch (e: StaticError) {
                // Expected - this is good
            } catch (e: NotImplementedError) {
                // Also acceptable for invalid examples
            }
        }
    }
})

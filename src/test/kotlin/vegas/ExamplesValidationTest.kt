package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import vegas.frontend.compileToIR
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

    // Examples excluded from this test due to known language design limitations.
    // These are tested elsewhere (see comments) to ensure they remain valid.
    val knownLanguageLimitations = setOf(
        // MontyHallChance: Demonstrates the declaration/definition split for hidden values.
        // The constraint "Host.goat != Host.car" belongs logically at the declaration site
        // (where Host.car is yielded as hidden), but can only be verified server-side at
        // the reveal site. Current language syntax doesn't support deferred constraints
        // (e.g., "where reveal Host.car != Host.goat").
        // NOTE: IR compilation is tested in UnrollerTest.kt ("produces identical EFG for MontyHallChance")
        "MontyHallChance"
    )

    // Examples known to fail the pot-conservation check (Pass E in typeCheck).
    // Either some branch underpays (funds get stuck in the contract) or overpays
    // (contract reverts at runtime). Listed here so they continue to parse and
    // compile to IR; rewriting them to be conservative is tracked in
    // docs/FUTURE.md. Lottery is the canonical case and is on the active TODO.
    val knownNonConservative = setOf(
        "ClaimFraud",
        "CommitteeVoting",
        "GasPriceAuction",
        "HiddenReserve",
        "Lottery",
        "StakingSlashing",
        "TwoRobotCorridor",
        "VickreyAuction",
    )

    val examples = exampleFiles
        .map { it.nameWithoutExtension }
        .filter { it !in knownLanguageLimitations }

    val typeCheckableExamples = examples.filter { it !in knownNonConservative }

    "All examples should parse successfully" - {
        withData(examples) { exampleName ->
            // This will throw if parsing fails
            parseFile("examples/$exampleName.vg")
        }
    }

    "All examples should typecheck successfully" - {
        withData(typeCheckableExamples) { exampleName ->
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

            // Pass E: pot conservation. Run on every typecheckable
            // example; the known-non-conservative ones are validated
            // separately below.
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)
            try {
                vegas.backend.gambit.verifyConservation(ir)
            } catch (e: vegas.backend.gambit.ConservationViolation) {
                throw AssertionError(
                    "$exampleName.vg fails the pot-conservation check (Pass E):\n${e.message}\n" +
                        "Either rewrite to conserve, or add to knownNonConservative."
                )
            }
        }
    }

    "Known-non-conservative examples fail the conservation check (Pass E)" - {
        withData(knownNonConservative) { exampleName ->
            val ast = parseFile("examples/$exampleName.vg")
            // Earlier passes must succeed - the conservation failure is
            // the only one we accept.
            typeCheck(ast)
            val ir = compileToIR(inlineMacros(ast))
            try {
                vegas.backend.gambit.verifyConservation(ir)
                throw AssertionError(
                    "$exampleName.vg is listed as known-non-conservative but now passes Pass E. " +
                        "Remove it from knownNonConservative."
                )
            } catch (_: vegas.backend.gambit.ConservationViolation) {
                // Expected.
            }
        }
    }

    "All examples should compile to IR successfully" - {
        withData(examples) { exampleName ->
            val ast = try {
                parseFile("examples/$exampleName.vg")
            } catch (e: Exception) {
                throw AssertionError("Failed to parse $exampleName.vg", e)
            }

            val inlined = try {
                inlineMacros(ast)
            } catch (e: Exception) {
                throw AssertionError("Failed to inline macros in $exampleName.vg", e)
            }

            try {
                compileToIR(inlined)
            } catch (e: Exception) {
                throw AssertionError("Failed to compile $exampleName.vg to IR", e)
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
            } catch (_: StaticError) {
                // Expected - this is good
            } catch (_: NotImplementedError) {
                // Also acceptable for invalid examples
            }
        }
    }
})

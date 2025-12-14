package vegas.backend.clarity

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import vegas.frontend.parseCode
import vegas.frontend.compileToIR
import java.io.File

class ClarityBackendTest {

    @Test
    fun testOddsEvensGeneration() {
        val code = """
            join Odd() ${'$'} 100 Even() ${'$'} 100;
            yield Odd(c: bool) Even(c: bool);
            withdraw (Even.c != null && Odd.c != null) ?
                 { Even -> ((Even.c <-> Odd.c) ? 126 : 74); Odd -> ((Even.c <-> Odd.c) ? 74 : 126) }
            : (Even.c == null && Odd.c != null) ? { Even -> 20; Odd -> 180 }
            : (Even.c != null && Odd.c == null) ? { Even -> 180; Odd -> 20 }
            : { Even -> 100; Odd -> 100 }
        """.trimIndent()

        val ast = parseCode(code)
        val ir = compileToIR(ast)
        val clarityCode = genClarity(ir)

        println(clarityCode)

        // Basic structural checks
        assertTrue(clarityCode.contains("(define-data-var total-pot uint u0)"))
        assertTrue(clarityCode.contains("(define-data-var role-odd (optional principal) none)"))
        assertTrue(clarityCode.contains("(define-data-var role-even (optional principal) none)"))

        // Check for commit/reveal expansion
        // Should have commit vars
        assertTrue(clarityCode.contains("(define-data-var commit-odd-c (optional (buff 32)) none)"))
        assertTrue(clarityCode.contains("(define-data-var commit-even-c (optional (buff 32)) none)"))

        // Check for reveal vars (values)
        assertTrue(clarityCode.contains("(define-data-var var-odd-c bool false)"))
        assertTrue(clarityCode.contains("(define-data-var var-even-c bool false)"))

        // Check for map
        assertTrue(clarityCode.contains("(define-map action-done uint bool)"))
        assertFalse(clarityCode.contains("(define-data-var state uint"))

        // Check for registration functions
        assertTrue(clarityCode.contains("(define-public (register-odd"))
        assertTrue(clarityCode.contains("(define-public (register-even"))

        // Check for timeout
        assertTrue(clarityCode.contains("(define-public (timeout)"))

        // Check for withdraw
        assertTrue(clarityCode.contains("(define-public (withdraw)"))
    }
}

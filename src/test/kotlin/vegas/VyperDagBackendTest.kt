package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.backend.vyper.genVyper
import vegas.frontend.parseFile
import vegas.frontend.compileToIR

/**
 * Tests for DAG-based Vyper backend.
 * Mirrors SolidityDagBackendTest.kt to ensure semantic equivalence.
 */
class VyperDagBackendTest : FreeSpec({

    "DAG-based Vyper generation" - {

        "should generate contract without phase variable" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should NOT have phase variable
            vyperCode shouldNotContain "phase: uint256"

            // Should have actionDone mapping
            vyperCode shouldContain "actionDone: HashMap[uint256, bool]"

            // Should have actionTimestamp mapping
            vyperCode shouldContain "actionTimestamp: HashMap[uint256, uint256]"

            // Should have ACTION constants
            vyperCode shouldContain "ACTION_"
            vyperCode shouldContain ": constant(uint256)"
        }

        "should not generate modifiers (Vyper doesn't have them)" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should NOT have modifiers
            vyperCode shouldNotContain "modifier"

            // Should have inline asserts instead
            vyperCode shouldContain "assert"
            vyperCode shouldContain "dependency not satisfied"
            vyperCode shouldContain "already done"
            vyperCode shouldContain "bad role"
        }

        "should generate action functions with inline dependency checks" {
            val ast = parseFile("examples/Prisoners.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have move_ functions
            vyperCode shouldContain "def move_"

            // Should set actionDone with self. prefix
            vyperCode shouldContain "self.actionDone["
            vyperCode shouldContain "] = True"

            // Should set actionTimestamp
            vyperCode shouldContain "self.actionTimestamp["

            // Should have dependency assertions
            vyperCode shouldContain "assert self.actionDone["
        }

        "should handle commit-reveal correctly" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have hidden parameter storage
            vyperCode shouldContain "_hidden_"

            // Should have keccak256 verification in reveal
            vyperCode shouldContain "keccak256"
            vyperCode shouldContain "bad reveal"

            // Should have _checkReveal helper
            vyperCode shouldContain "def _checkReveal"
            vyperCode shouldContain "@internal"
            vyperCode shouldContain "@view"

            // Should use abi_encode with output_type
            vyperCode shouldContain "abi_encode"
            vyperCode shouldContain "output_type=Bytes[128]"
        }

        "should use Python-style syntax" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should use True/False (capitalized)
            vyperCode shouldContain "True"
            vyperCode shouldContain "False"
            vyperCode shouldNotContain "true"
            vyperCode shouldNotContain "false"

            // Should use and/or/not (words)
            vyperCode shouldContain " or "
            vyperCode shouldContain "not "

            // Should use self. prefix for storage
            vyperCode shouldContain "self."

            // Should use decorators
            vyperCode shouldContain "@external"
            vyperCode shouldContain "@internal"
        }

        "should have proper function decorators" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Join functions should be @payable
            vyperCode shouldContain "@payable"

            // Helper functions should be @internal
            vyperCode shouldContain "@internal"

            // Action functions should be @external
            vyperCode shouldContain "@external"

            // View functions should be @view
            vyperCode shouldContain "@view"
        }

        "should generate proper enum syntax" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have enum with indentation
            vyperCode shouldContain "enum Role:"
            vyperCode shouldContain "    None"

            // Should use enum values with dot notation
            vyperCode shouldContain "Role.None"
        }

        "should use HashMap instead of mapping" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should use HashMap
            vyperCode shouldContain "HashMap["

            // Should NOT use mapping
            vyperCode shouldNotContain "mapping("
        }

        "should generate withdraw with raw_call" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should use raw_call for ETH transfer
            vyperCode shouldContain "raw_call"
            vyperCode shouldContain "convert(bal, uint256)"
            vyperCode shouldContain "max_outsize=0"

            // Should NOT use .call{value:...}
            vyperCode shouldNotContain ".call{"
        }

        "should generate __default__ fallback function" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have __default__ function
            vyperCode shouldContain "def __default__():"
            vyperCode shouldContain "direct ETH not allowed"

            // Should NOT use receive() or fallback()
            vyperCode shouldNotContain "receive()"
            vyperCode shouldNotContain "fallback()"
        }

        "should have version pragma" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have version comment
            vyperCode shouldContain "# @version 0.4.0"
        }

        "should generate deterministic output" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val output1 = genVyper(ir)
            val output2 = genVyper(ir)

            output1 shouldBe output2
        }

        "should handle domain guards with or chains" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have domain validation with or
            vyperCode shouldContain " or "
            vyperCode shouldContain "\"domain\""
        }

        "should handle where clauses" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have where clause assertions
            vyperCode shouldContain "\"where\""

            // Should reference other player's values
            vyperCode shouldContain "self.Guest_d"
            vyperCode shouldContain "self.Host_goat"
        }

        "should generate payoff distribution" {
            val ast = parseFile("examples/Prisoners.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have distributePayoffs function
            vyperCode shouldContain "def distributePayoffs():"

            // Should check FINAL_ACTION
            vyperCode shouldContain "FINAL_ACTION"
            vyperCode shouldContain "game not over"

            // Should check payoffs_distributed flag
            vyperCode shouldContain "payoffs_distributed"
            vyperCode shouldContain "payoffs already sent"

            // Should assign to balanceOf
            vyperCode shouldContain "self.balanceOf["
        }

        "should handle role addresses correctly" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val vyperCode = genVyper(ir)

            // Should have address_Role storage
            vyperCode shouldContain "address_"
            vyperCode shouldContain ": address"

            // Should save address during join
            vyperCode shouldContain "self.address_"
            vyperCode shouldContain "= msg.sender"
        }
    }
})

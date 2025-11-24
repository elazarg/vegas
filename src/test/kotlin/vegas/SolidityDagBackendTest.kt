package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.backend.solidity.genSolidity
import vegas.frontend.parseFile
import vegas.frontend.compileToIR

/**
 * Tests for DAG-based Solidity backend.
 */
class SolidityDagBackendTest : FreeSpec({

    "DAG-based Solidity generation" - {

        "should generate contract without phase variable" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val solidityCode = genSolidity(ir)

            // Should NOT have phase variable
            solidityCode shouldNotContain "uint256 public phase"

            // Should have actionDone mapping
            solidityCode shouldContain "mapping(uint256 => bool) public actionDone"

            // Should have actionTimestamp mapping
            solidityCode shouldContain "mapping(uint256 => uint256) public actionTimestamp"

            // Should have ACTION constants (note: keyword order is "constant public")
            solidityCode shouldContain "uint256 constant public ACTION_"
        }

        "should generate depends and notDone modifiers" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)

            val solidityCode = genSolidity(ir)

            // Should have depends modifier
            solidityCode shouldContain "modifier depends(uint256 actionId)"
            solidityCode shouldContain "actionDone[actionId]"

            // Should have notDone modifier
            solidityCode shouldContain "modifier notDone(uint256 actionId)"
            solidityCode shouldContain "!actionDone[actionId]"
        }

        "should generate action functions with dependency modifiers" {
            val ast = parseFile("examples/Prisoners.vg")
            val ir = compileToIR(ast)

            val solidityCode = genSolidity(ir)

            // Should have move_ functions instead of phase-based functions
            solidityCode shouldContain "function move_"

            // Should set actionDone in function bodies
            solidityCode shouldContain "actionDone["
            solidityCode shouldContain "] = true"

            // Should set actionTimestamp
            solidityCode shouldContain "actionTimestamp["
        }

        "should handle commit-reveal correctly" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)

            val solidityCode = genSolidity(ir)

            // Should still have hidden parameter storage
            solidityCode shouldContain "hidden_"

            // Should have keccak verification in reveal
            solidityCode shouldContain "keccak256"
            solidityCode shouldContain "bad reveal"
        }

    }
})

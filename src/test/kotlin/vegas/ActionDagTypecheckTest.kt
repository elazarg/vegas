package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import vegas.frontend.parseFile

/**
 * Tests that invalid ActionDag structures are rejected by the typechecker.
 */
class ActionDagTypecheckTest : FreeSpec({

    "typechecker should reject invalid DAG structures" - {

        "should reject reading hidden field before reveal" {
            val ast = parseFile("examples/Invalid_ReadHiddenField.vg")

            var caught = false
            try {
                typeCheck(ast)
            } catch (_: StaticError) {
                // Either the existing checker or ActionDag validator should catch this
                caught = true
            }

            caught shouldBe true
        }
    }

    "typechecker should accept valid games" - {

        "should accept Simple.vg" {
            val ast = parseFile("examples/Simple.vg")
            var threw = false
            try {
                typeCheck(ast)
            } catch (_: StaticError) {
                threw = true
            }
            threw shouldBe false
        }

        "should accept Prisoners.vg" {
            val ast = parseFile("examples/Prisoners.vg")
            var threw = false
            try {
                typeCheck(ast)
            } catch (_: StaticError) {
                threw = true
            }
            threw shouldBe false
        }

        "should accept MontyHall.vg" {
            val ast = parseFile("examples/MontyHall.vg")
            var threw = false
            try {
                typeCheck(ast)
            } catch (_: StaticError) {
                threw = true
            }
            threw shouldBe false
        }
    }
})

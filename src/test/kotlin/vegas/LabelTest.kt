package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeSameInstanceAs
import vegas.ir.ActionId
import vegas.ir.Expr
import vegas.semantics.Label
import vegas.semantics.PlayTag

/**
 * Test suite for Label types.
 *
 * Tests the label abstractions that represent transitions in the LTS.
 */
class LabelTest : FreeSpec({

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")

    "Play label" - {

        "contains role and delta" {
            val aliceField = FieldRef(alice, VarId("x"))
            val delta = mapOf(aliceField to Expr.Const.BoolVal(true))
            val actionId: ActionId = alice to 0

            val play = Label.Play(
                role = alice,
                delta = delta,
                tag = PlayTag.Action(actionId)
            )

            play.role shouldBe alice
            play.delta shouldBe delta
            play.tag shouldBe PlayTag.Action(actionId)
        }

        "supports quit moves" {
            val aliceField = FieldRef(alice, VarId("x"))
            val delta = mapOf(aliceField to Expr.Const.Quit)

            val play = Label.Play(
                role = alice,
                delta = delta,
                tag = PlayTag.Quit
            )

            play.role shouldBe alice
            play.delta shouldBe delta
            play.tag shouldBe PlayTag.Quit
        }

        "can have multiple field assignments" {
            val field1 = FieldRef(bob, VarId("x"))
            val field2 = FieldRef(bob, VarId("y"))
            val delta = mapOf(
                field1 to Expr.Const.BoolVal(false),
                field2 to Expr.Const.IntVal(42)
            )
            val actionId: ActionId = bob to 1

            val play = Label.Play(
                role = bob,
                delta = delta,
                tag = PlayTag.Action(actionId)
            )

            play.delta.size shouldBe 2
            play.delta[field1] shouldBe Expr.Const.BoolVal(false)
            play.delta[field2] shouldBe Expr.Const.IntVal(42)
        }
    }

    "PlayTag.Action" - {

        "preserves actionId" {
            val actionId: ActionId = alice to 2
            val tag = PlayTag.Action(actionId)

            tag.actionId shouldBe actionId
        }

        "different actionIds create different tags" {
            val tag1 = PlayTag.Action(alice to 0)
            val tag2 = PlayTag.Action(alice to 1)

            (tag1 == tag2) shouldBe false
        }

        "same actionId creates equal tags" {
            val actionId: ActionId = bob to 0
            val tag1 = PlayTag.Action(actionId)
            val tag2 = PlayTag.Action(actionId)

            tag1 shouldBe tag2
        }
    }

    "PlayTag.Quit" - {

        "is a singleton object" {
            val quit1 = PlayTag.Quit
            val quit2 = PlayTag.Quit

            quit1 shouldBeSameInstanceAs quit2
        }
    }

    "Label.FinalizeFrontier" - {

        "is a singleton object" {
            val finalize1 = Label.FinalizeFrontier
            val finalize2 = Label.FinalizeFrontier

            finalize1 shouldBeSameInstanceAs finalize2
        }

        "is distinct from Play labels" {
            val play = Label.Play(
                role = alice,
                delta = emptyMap(),
                tag = PlayTag.Quit
            )

            val finalize = Label.FinalizeFrontier

            (play == finalize) shouldBe false
        }
    }

    "Label sealed class hierarchy" - {

        "Play and FinalizeFrontier are distinct" {
            val play: Label = Label.Play(
                role = alice,
                delta = emptyMap(),
                tag = PlayTag.Quit
            )
            val finalize: Label = Label.FinalizeFrontier

            when (play) {
                is Label.Play -> play.role shouldBe alice
                is Label.FinalizeFrontier -> error("Should not be FinalizeFrontier")
            }

            when (finalize) {
                is Label.Play -> error("Should not be Play")
                is Label.FinalizeFrontier -> finalize shouldBeSameInstanceAs Label.FinalizeFrontier
            }
        }
    }
})

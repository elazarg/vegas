package vegas.backend.gambit

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeSameInstanceAs
import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionId

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
            val delta = mapOf(aliceField to IrVal.BoolVal(true))
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
            val delta = mapOf(aliceField to IrVal.Quit)

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
                field1 to IrVal.BoolVal(false),
                field2 to IrVal.IntVal(42)
            )
            val actionId: ActionId = bob to 1

            val play = Label.Play(
                role = bob,
                delta = delta,
                tag = PlayTag.Action(actionId)
            )

            play.delta.size shouldBe 2
            play.delta[field1] shouldBe IrVal.BoolVal(false)
            play.delta[field2] shouldBe IrVal.IntVal(42)
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

    "Label.CommitFrontier" - {

        "is a singleton object" {
            val commit1 = Label.CommitFrontier
            val commit2 = Label.CommitFrontier

            commit1 shouldBeSameInstanceAs commit2
        }

        "is distinct from Play labels" {
            val play = Label.Play(
                role = alice,
                delta = emptyMap(),
                tag = PlayTag.Quit
            )

            val commit = Label.CommitFrontier

            (play == commit) shouldBe false
        }
    }

    "Label sealed class hierarchy" - {

        "Play and CommitFrontier are distinct" {
            val play: Label = Label.Play(
                role = alice,
                delta = emptyMap(),
                tag = PlayTag.Quit
            )
            val commit: Label = Label.CommitFrontier

            when (play) {
                is Label.Play -> play.role shouldBe alice
                is Label.CommitFrontier -> error("Should not be CommitFrontier")
            }

            when (commit) {
                is Label.Play -> error("Should not be Play")
                is Label.CommitFrontier -> commit shouldBeSameInstanceAs Label.CommitFrontier
            }
        }
    }
})

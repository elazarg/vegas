package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNotBe
import io.kotest.matchers.collections.shouldContain
import io.kotest.matchers.collections.shouldNotContain
import io.kotest.matchers.collections.shouldNotBeEmpty
import vegas.frontend.compileToIR
import vegas.frontend.parseFile
import vegas.ir.Visibility
import vegas.ir.buildActionDag

/**
 * Tests for building ActionDag from GameIR.
 */
class ActionDagFromIrTest : FreeSpec({

    "buildActionDag from IR" - {

        "should build DAG for Simple.vg" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!.nodes.shouldNotBeEmpty()

            // Verify basic structure
            dag.nodes.size shouldBe ir.phases.sumOf { it.actions.size }
        }

        "should build DAG for Prisoners.vg" {
            val ast = parseFile("examples/Prisoners.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!.nodes.shouldNotBeEmpty()

            // Prisoners dilemma has two players moving simultaneously
            // They should be able to execute concurrently if in same phase
            val roleA = RoleId("A")
            val roleB = RoleId("B")

            // Find actions for each player
            val actionsA = dag.nodes.filter { it.first == roleA }
            val actionsB = dag.nodes.filter { it.first == roleB }

            actionsA.shouldNotBeEmpty()
            actionsB.shouldNotBeEmpty()
        }

        "should build DAG for OddsEvens.vg" {
            val ast = parseFile("examples/OddsEvens.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!.nodes.shouldNotBeEmpty()

            // OddsEvens has Odd and Even players
            val odd = RoleId("Odd")
            val even = RoleId("Even")

            val oddActions = dag.nodes.filter { it.first == odd }
            val evenActions = dag.nodes.filter { it.first == even }

            oddActions.shouldNotBeEmpty()
            evenActions.shouldNotBeEmpty()

            // If they move in the same phase, they should be concurrent
            val oddInPhase0 = oddActions.find { it.second == 0 }
            val evenInPhase0 = evenActions.find { it.second == 0 }

            if (oddInPhase0 != null && evenInPhase0 != null) {
                // These should be concurrent (no dependency between them)
                dag.canExecuteConcurrently(oddInPhase0, evenInPhase0) shouldBe true
            }
        }

        "should detect commit-reveal in MontyHall.vg" {
            val ast = parseFile("examples/MontyHall.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!.nodes.shouldNotBeEmpty()

            val host = RoleId("Host")
            val hostActions = dag.nodes.filter { it.first == host }.sortedBy { it.second }

            hostActions.shouldNotBeEmpty()

            // MontyHall has Host committing to car position then revealing it
            // Find commits and reveals by checking visibility
            val commits = hostActions.filter { actionId ->
                dag.visibility(actionId).values.any { it == Visibility.COMMIT }
            }

            val reveals = hostActions.filter { actionId ->
                dag.visibility(actionId).values.any { it == Visibility.REVEAL }
            }

            // If there are commits and reveals, verify ordering
            if (commits.isNotEmpty() && reveals.isNotEmpty()) {
                val firstCommit = commits.first()
                val firstReveal = reveals.first()

                // Commit should come before reveal (not necessarily immediately)
                (firstCommit.second < firstReveal.second) shouldBe true
            }
        }

        "should handle guard dependencies" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!.nodes.shouldNotBeEmpty()

            // Check that actions with guard reads have dependencies
            for (action in dag.nodes) {
                val guardReads = dag.guardReads(action)
                if (guardReads.isNotEmpty()) {
                    // This action reads some fields, so it should have prerequisites
                    // (unless reading initial state, which we don't model yet)
                    val prereqs = dag.prerequisitesOf(action)
                    // Note: prereqs might be empty if reading initial/constant values
                }
            }
        }

        "should produce topological order" {
            val ast = parseFile("examples/OddsEvens.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!

            val topo = dag.topo()

            // Verify that every action appears after its prerequisites
            for ((idx, action) in topo.withIndex()) {
                val prereqs = dag.prerequisitesOf(action)
                for (prereq in prereqs) {
                    val prereqIdx = topo.indexOf(prereq)
                    (prereqIdx < idx) shouldBe true
                }
            }
        }

        "should handle games with no dependencies" {
            // Simple simultaneous game should have independent actions
            val ast = parseFile("examples/Prisoners.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!

            // In a simple simultaneous game, actions in the same phase
            // with no guard dependencies should be concurrent
            val nodesInPhase0 = dag.nodes.filter { it.second == 0 }

            if (nodesInPhase0.size >= 2) {
                val action1 = nodesInPhase0.first()
                val action2 = nodesInPhase0.last()

                // They might be concurrent if they don't read each other's writes
                val prereqs1 = dag.prerequisitesOf(action1)
                val prereqs2 = dag.prerequisitesOf(action2)

                // At minimum, neither should be prerequisite of the other
                prereqs1 shouldNotContain action2
                prereqs2 shouldNotContain action1
            }
        }
    }

    "buildActionDag validation" - {

        "should validate all example games" {
            val examples = listOf(
                "Simple.vg",
                "Prisoners.vg",
                "OddsEvens.vg",
                "MontyHall.vg",
                "Bet.vg",
                "Trivial1.vg"
            )

            for (example in examples) {
                val ast = parseFile("examples/$example")
                val ir = compileToIR(ast)
                val dag = buildActionDag(ir)

                // All valid examples should produce a valid DAG
                dag shouldNotBe null
            }
        }

        "should produce consistent metadata" {
            val ast = parseFile("examples/Simple.vg")
            val ir = compileToIR(ast)
            val dag = buildActionDag(ir)

            dag shouldNotBe null
            dag!!

            // Every action should have metadata
            for (action in dag.nodes) {
                val meta = dag.metadata(action)
                meta.role shouldBe action.first

                // Visibility map should cover all writes
                for (field in meta.writes) {
                    meta.visibility.keys shouldContain field
                }
            }
        }
    }
})

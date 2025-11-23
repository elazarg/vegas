package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNotBe
import io.kotest.matchers.collections.shouldContain
import io.kotest.matchers.collections.shouldContainAll
import vegas.ir.ActionDag
import vegas.ir.ActionId
import vegas.ir.ActionMetadata
import vegas.ir.Visibility

/**
 * Tests for ActionDag construction and validation in isolation
 * (without IR integration).
 */
class ActionDagCoreTest : FreeSpec({

    // Test helpers
    fun role(name: String) = RoleId(name)
    fun field(role: String, varName: String) = FieldRef(RoleId(role), VarId(varName))

    val alice = role("Alice")
    val bob = role("Bob")

    "ActionDag construction" - {

        "should build a simple chain DAG (a -> b -> c)" {
            val actionA: ActionId = alice to 0
            val actionB: ActionId = alice to 1
            val actionC: ActionId = alice to 2

            val nodes = setOf(actionA, actionB, actionC)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> emptySet()
                    actionB -> setOf(actionA)
                    actionC -> setOf(actionB)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.nodes shouldBe nodes
            dag.topo() shouldContainAll listOf(actionA, actionB, actionC)

            // Verify ordering: actionA before actionB, actionB before actionC
            val topoList = dag.topo()
            topoList.indexOf(actionA) shouldBe 0
            topoList.indexOf(actionB) shouldBe 1
            topoList.indexOf(actionC) shouldBe 2
        }

        "should build a diamond DAG (a -> b, a -> c, {b,c} -> d)" {
            val actionA: ActionId = alice to 0
            val actionB: ActionId = alice to 1
            val actionC: ActionId = bob to 1
            val actionD: ActionId = alice to 2

            val nodes = setOf(actionA, actionB, actionC, actionD)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> emptySet()
                    actionB -> setOf(actionA)
                    actionC -> setOf(actionA)
                    actionD -> setOf(actionB, actionC)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.nodes shouldBe nodes

            // actionB and actionC should both depend on actionA
            dag.prerequisitesOf(actionB) shouldContain actionA
            dag.prerequisitesOf(actionC) shouldContain actionA

            // actionD should depend on both actionB and actionC
            dag.prerequisitesOf(actionD) shouldContainAll listOf(actionB, actionC)

            // actionB and actionC should be concurrent
            dag.canExecuteConcurrently(actionB, actionC) shouldBe true
        }

        "should reject cyclic DAGs (a -> b, b -> a)" {
            val actionA: ActionId = alice to 0
            val actionB: ActionId = alice to 1

            val nodes = setOf(actionA, actionB)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> setOf(actionB)  // cycle!
                    actionB -> setOf(actionA)  // cycle!
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldBe null  // Should reject due to cycle
        }

        "should reject self-loops (a -> a)" {
            val actionA: ActionId = alice to 0

            val nodes = setOf(actionA)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> setOf(actionA)  // self-loop!
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldBe null  // Should reject due to cycle
        }
    }

    "ActionDag commit-reveal validation" - {

        "should accept valid commit->reveal ordering" {
            val commit: ActionId = alice to 0
            val reveal: ActionId = alice to 1

            val fieldX = field("Alice", "x")

            val nodes = setOf(commit, reveal)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    commit -> emptySet()
                    reveal -> setOf(commit)  // reveal depends on commit
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    commit -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.COMMIT),
                        guardReads = emptySet()
                    )
                    reveal -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.REVEAL),
                        guardReads = emptySet()
                    )
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.prerequisitesOf(reveal) shouldContain commit
        }

        "should reject reveal before commit" {
            val commit: ActionId = alice to 1
            val reveal: ActionId = alice to 0

            val fieldX = field("Alice", "x")

            val nodes = setOf(commit, reveal)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    commit -> setOf(reveal)  // backwards! commit depends on reveal
                    reveal -> emptySet()
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    commit -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.COMMIT),
                        guardReads = emptySet()
                    )
                    reveal -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.REVEAL),
                        guardReads = emptySet()
                    )
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldBe null  // Should reject: reveal not reachable from commit
        }

        "should accept independent commits and reveals for different fields" {
            val commitX: ActionId = alice to 0
            val commitY: ActionId = bob to 0
            val revealX: ActionId = alice to 1
            val revealY: ActionId = bob to 1

            val fieldX = field("Alice", "x")
            val fieldY = field("Bob", "y")

            val nodes = setOf(commitX, commitY, revealX, revealY)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    commitX, commitY -> emptySet()
                    revealX -> setOf(commitX)
                    revealY -> setOf(commitY)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    commitX -> ActionMetadata(alice, setOf(fieldX), mapOf(fieldX to Visibility.COMMIT), emptySet())
                    commitY -> ActionMetadata(bob, setOf(fieldY), mapOf(fieldY to Visibility.COMMIT), emptySet())
                    revealX -> ActionMetadata(alice, setOf(fieldX), mapOf(fieldX to Visibility.REVEAL), emptySet())
                    revealY -> ActionMetadata(bob, setOf(fieldY), mapOf(fieldY to Visibility.REVEAL), emptySet())
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
        }
    }

    "ActionDag visibility validation" - {

        "should accept reading PUBLIC fields from predecessors" {
            val writeX: ActionId = alice to 0
            val readX: ActionId = bob to 1

            val fieldX = field("Alice", "x")

            val nodes = setOf(writeX, readX)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    writeX -> emptySet()
                    readX -> setOf(writeX)  // readX depends on writeX
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    writeX -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.PUBLIC),
                        guardReads = emptySet()
                    )
                    readX -> ActionMetadata(
                        role = bob,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = setOf(fieldX)  // reads Alice.x
                    )
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
        }

        "should accept reading REVEALed fields from predecessors" {
            val commit: ActionId = alice to 0
            val reveal: ActionId = alice to 1
            val read: ActionId = bob to 2

            val fieldX = field("Alice", "x")

            val nodes = setOf(commit, reveal, read)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    commit -> emptySet()
                    reveal -> setOf(commit)
                    read -> setOf(reveal)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    commit -> ActionMetadata(alice, setOf(fieldX), mapOf(fieldX to Visibility.COMMIT), emptySet())
                    reveal -> ActionMetadata(alice, setOf(fieldX), mapOf(fieldX to Visibility.REVEAL), emptySet())
                    read -> ActionMetadata(bob, emptySet(), emptyMap(), setOf(fieldX))
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
        }

        "should reject reading hidden (COMMIT) fields before reveal" {
            val commit: ActionId = alice to 0
            val read: ActionId = bob to 1  // tries to read before reveal

            val fieldX = field("Alice", "x")

            val nodes = setOf(commit, read)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    commit -> emptySet()
                    read -> setOf(commit)  // depends on commit, but commit is COMMIT (hidden)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                when (action) {
                    commit -> ActionMetadata(
                        role = alice,
                        writes = setOf(fieldX),
                        visibility = mapOf(fieldX to Visibility.COMMIT),
                        guardReads = emptySet()
                    )
                    read -> ActionMetadata(
                        role = bob,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = setOf(fieldX)  // tries to read hidden field
                    )
                    else -> error("Unknown action")
                }
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldBe null  // Should reject: cannot read hidden field
        }
    }

    "ActionDag concurrency detection" - {

        "should detect concurrent actions correctly" {
            val actionA: ActionId = alice to 0
            val actionB: ActionId = alice to 1
            val actionC: ActionId = bob to 1

            val nodes = setOf(actionA, actionB, actionC)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> emptySet()
                    actionB -> setOf(actionA)
                    actionC -> setOf(actionA)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.canExecuteConcurrently(actionB, actionC) shouldBe true  // actionB and actionC are concurrent
            dag.canExecuteConcurrently(actionA, actionB) shouldBe false   // actionA must happen before actionB
            dag.canExecuteConcurrently(actionA, actionC) shouldBe false   // actionA must happen before actionC
        }

        "should detect non-concurrent actions in a chain" {
            val actionA: ActionId = alice to 0
            val actionB: ActionId = alice to 1
            val actionC: ActionId = alice to 2

            val nodes = setOf(actionA, actionB, actionC)
            val prereqs: (ActionId) -> Set<ActionId> = { action ->
                when (action) {
                    actionA -> emptySet()
                    actionB -> setOf(actionA)
                    actionC -> setOf(actionB)
                    else -> emptySet()
                }
            }
            val metadata: (ActionId) -> ActionMetadata = { action ->
                ActionMetadata(
                    role = action.first,
                    writes = setOf(field(action.first.name, "var${action.second}")),
                    visibility = mapOf(field(action.first.name, "var${action.second}") to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.canExecuteConcurrently(actionA, actionB) shouldBe false
            dag.canExecuteConcurrently(actionB, actionC) shouldBe false
            dag.canExecuteConcurrently(actionA, actionC) shouldBe false
        }
    }

    "ActionDag metadata queries" - {

        "should provide correct metadata for actions" {
            val action: ActionId = alice to 0

            val fieldX = field("Alice", "x")

            val nodes = setOf(action)
            val prereqs: (ActionId) -> Set<ActionId> = { emptySet() }
            val metadata: (ActionId) -> ActionMetadata = {
                ActionMetadata(
                    role = alice,
                    writes = setOf(fieldX),
                    visibility = mapOf(fieldX to Visibility.PUBLIC),
                    guardReads = emptySet()
                )
            }

            val dag = ActionDag.from(nodes, prereqs, metadata)

            dag shouldNotBe null
            dag!!.owner(action) shouldBe alice
            dag.writes(action) shouldBe setOf(fieldX)
            dag.visibility(action) shouldBe mapOf(fieldX to Visibility.PUBLIC)
            dag.guardReads(action) shouldBe emptySet()
        }
    }
})

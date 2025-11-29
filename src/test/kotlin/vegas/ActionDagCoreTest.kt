package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNotBe
import vegas.ir.*

/**
 * Core unit tests for ActionDag with synthetic test cases.
 * These tests verify ActionDag behavior in isolation, without IR dependencies.
 */
class ActionDagCoreTest : FreeSpec({

    "ActionDag.fromGraph with synthetic DAGs" - {

        "should create simple chain A -> B -> C" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")
            val roleC = RoleId("C")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 1
            val c: ActionId = roleC to 2

            val nodes = setOf(a, b, c)
            val deps = mapOf(
                a to emptySet(),
                b to setOf(a),
                c to setOf(b)
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            val dag = ActionDag.fromGraph(nodes, deps, payloads)

            dag shouldNotBe null
            dag!!.nodes.size shouldBe 3

            // Verify topological order: A before B before C
            val topo = dag.topo()
            val aIdx = topo.indexOf(a)
            val bIdx = topo.indexOf(b)
            val cIdx = topo.indexOf(c)

            (aIdx < bIdx) shouldBe true
            (bIdx < cIdx) shouldBe true
        }

        "should create diamond A -> {B, C} -> D" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")
            val roleC = RoleId("C")
            val roleD = RoleId("D")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 1
            val c: ActionId = roleC to 2
            val d: ActionId = roleD to 3

            val nodes = setOf(a, b, c, d)
            val deps = mapOf(
                a to emptySet(),
                b to setOf(a),
                c to setOf(a),
                d to setOf(b, c)
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            val dag = ActionDag.fromGraph(nodes, deps, payloads)

            dag shouldNotBe null
            dag!!.nodes.size shouldBe 4

            // B and C should be concurrent (no dependency between them)
            dag.canExecuteConcurrently(b, c) shouldBe true

            // A should reach D
            dag.reaches(a, d) shouldBe true

            // D should not reach A (no back edges)
            dag.reaches(d, a) shouldBe false
        }

        "should reject cyclic graph A -> B -> A" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 1

            val nodes = setOf(a, b)
            val deps = mapOf(
                a to setOf(b),  // A depends on B
                b to setOf(a)   // B depends on A -> cycle!
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            // Cyclic graph should throw an exception (from ExplicitDag.from)
            var exceptionThrown = false
            try {
                ActionDag.fromGraph(nodes, deps, payloads)
            } catch (e: IllegalArgumentException) {
                exceptionThrown = true
                e.message shouldBe "Cycle detected"
            }

            exceptionThrown shouldBe true
        }

        "should handle independent concurrent actions" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")
            val roleC = RoleId("C")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 0
            val c: ActionId = roleC to 0

            val nodes = setOf(a, b, c)
            val deps = mapOf(
                a to emptySet<ActionId>(),
                b to emptySet(),
                c to emptySet()
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            val dag = ActionDag.fromGraph(nodes, deps, payloads)

            dag shouldNotBe null
            dag!!.nodes.size shouldBe 3

            // All actions are concurrent
            dag.canExecuteConcurrently(a, b) shouldBe true
            dag.canExecuteConcurrently(b, c) shouldBe true
            dag.canExecuteConcurrently(a, c) shouldBe true
        }
    }

    "ActionDag topological ordering" - {

        "should order predecessors before dependents" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")
            val roleC = RoleId("C")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 1
            val c: ActionId = roleC to 2

            val nodes = setOf(a, b, c)
            val deps = mapOf(
                a to emptySet(),
                b to setOf(a),
                c to setOf(a, b)
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            val dag = ActionDag.fromGraph(nodes, deps, payloads)!!
            val topo = dag.topo()

            // For every action, all its prerequisites should come earlier
            for ((idx, action) in topo.withIndex()) {
                val prereqs = dag.prerequisitesOf(action)
                for (prereq in prereqs) {
                    val prereqIdx = topo.indexOf(prereq)
                    (prereqIdx < idx) shouldBe true
                }
            }
        }
    }

    "ActionDag concurrency" - {

        "canExecuteConcurrently should match reachability" {
            val roleA = RoleId("A")
            val roleB = RoleId("B")
            val roleC = RoleId("C")

            val a: ActionId = roleA to 0
            val b: ActionId = roleB to 1
            val c: ActionId = roleC to 2

            val nodes = setOf(a, b, c)
            val deps = mapOf(
                a to emptySet(),
                b to setOf(a),
                c to emptySet()  // C is independent
            )

            val payloads = nodes.associateWith { id ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(
                        params = emptyList(),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = id.first,
                        writes = emptySet(),
                        visibility = emptyMap(),
                        guardReads = emptySet()
                    )
                )
            }

            val dag = ActionDag.fromGraph(nodes, deps, payloads)!!

            // A and B are sequential (A -> B)
            dag.canExecuteConcurrently(a, b) shouldBe false
            dag.canExecuteConcurrently(b, a) shouldBe false

            // C is concurrent with both A and B
            dag.canExecuteConcurrently(a, c) shouldBe true
            dag.canExecuteConcurrently(c, a) shouldBe true
            dag.canExecuteConcurrently(b, c) shouldBe true
            dag.canExecuteConcurrently(c, b) shouldBe true
        }
    }

    "ActionDag commit/reveal validation" - {

        "should reject reveal without prior commit" {
            val roleA = RoleId("A")
            val field = FieldRef(roleA, VarId("x"))

            val a: ActionId = roleA to 0

            val nodes = setOf(a)
            val deps = mapOf(a to emptySet<ActionId>())

            val payloads = mapOf(
                a to ActionMeta(
                    id = a,
                    spec = ActionSpec(
                        params = listOf(ActionParam(VarId("x"), Type.IntType)),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = roleA,
                        writes = setOf(field),
                        visibility = mapOf(field to Visibility.REVEAL),  // Reveal without commit!
                        guardReads = emptySet()
                    )
                )
            )

            val dag = ActionDag.fromGraph(nodes, deps, payloads)

            // Should fail validation (reveal without commit)
            dag shouldBe null
        }

        "should accept reveal after commit" {
            val roleA = RoleId("A")
            val field = FieldRef(roleA, VarId("x"))

            val commit: ActionId = roleA to 0
            val reveal: ActionId = roleA to 1

            val nodes = setOf(commit, reveal)
            val deps = mapOf(
                commit to emptySet(),
                reveal to setOf(commit)
            )

            val payloads = mapOf(
                commit to ActionMeta(
                    id = commit,
                    spec = ActionSpec(
                        params = listOf(ActionParam(VarId("x"), Type.IntType)),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = roleA,
                        writes = setOf(field),
                        visibility = mapOf(field to Visibility.COMMIT),
                        guardReads = emptySet()
                    )
                ),
                reveal to ActionMeta(
                    id = reveal,
                    spec = ActionSpec(
                        params = listOf(ActionParam(VarId("x"), Type.IntType)),
                        join = null,
                        guardExpr = Expr.Const.BoolVal(true)
                    ),
                    struct = ActionStruct(
                        role = roleA,
                        writes = setOf(field),
                        visibility = mapOf(field to Visibility.REVEAL),
                        guardReads = emptySet()
                    )
                )
            )

            val dag = ActionDag.fromGraph(nodes, deps, payloads)

            // Should succeed (commit -> reveal)
            dag shouldNotBe null
            dag!!.reaches(commit, reveal) shouldBe true
        }
    }
})

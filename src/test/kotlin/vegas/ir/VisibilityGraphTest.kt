package vegas.ir

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import vegas.RoleId
import vegas.VarId
import vegas.FieldRef

class VisibilityGraphTest {

    private val alice = RoleId("Alice")
    private val bob = RoleId("Bob")
    private val x = VarId("x")
    private val y = VarId("y")

    // Helper to create minimal ActionDag for testing
    // We don't need full payloads, just enough to satisfy VisibilityGraphBuilder
    private fun createDag(
        actions: Set<ActionId>,
        deps: Map<ActionId, Set<ActionId>>,
        owners: Map<ActionId, RoleId>,
        visibilities: Map<ActionId, Visibility>
    ): ActionDag {
        // Mocking ActionMeta, Struct, Spec is tedious.
        // But ActionDag is open enough? No, constructor is private.
        // Use ActionDag.fromGraph

        val payloads = actions.associateWith { id ->
            val owner = owners[id]!!
            val vis = visibilities[id]!!

            val structVis = when(vis) {
                Visibility.COMMIT -> mapOf(FieldRef(owner, x) to Visibility.COMMIT)
                Visibility.REVEAL -> mapOf(FieldRef(owner, x) to Visibility.REVEAL) // Simplified
                Visibility.PUBLIC -> mapOf(FieldRef(owner, x) to Visibility.PUBLIC)
            }

            // inferKind logic:
            // hasCommit && !hasReveal -> COMMIT
            // hasReveal && !hasCommit -> REVEAL
            // else -> PUBLIC
            // To get desired 'vis', we construct structVis appropriately.

            ActionStruct(
                owner = owner,
                writes = structVis.keys,
                visibility = structVis,
                guardReads = emptySet()
            ).let { struct ->
                ActionMeta(
                    id = id,
                    spec = ActionSpec(emptyList(), null, Expr.Const.BoolVal(true)),
                    struct = struct
                )
            }
        }

        return ActionDag.fromGraph(actions, deps, payloads)
            ?: error("Failed to create ActionDag")
    }

    @Test
    fun `test simple public dependency`() {
        val a1 = alice to 1
        val b1 = bob to 1

        // A1 -> B1
        val dag = createDag(
            actions = setOf(a1, b1),
            deps = mapOf(b1 to setOf(a1)),
            owners = mapOf(a1 to alice, b1 to bob),
            visibilities = mapOf(a1 to Visibility.PUBLIC, b1 to Visibility.PUBLIC)
        )

        val vg = VisibilityGraphBuilder.build(dag)

        // A1 chain
        val a1_c = VisibilityNode(a1, ActionStep.COMMIT)
        val a1_h = VisibilityNode(a1, ActionStep.CHOOSE)
        val a1_r = VisibilityNode(a1, ActionStep.REVEAL)

        assertTrue(vg.dag.prerequisitesOf(a1_h).contains(a1_c))
        assertTrue(vg.dag.prerequisitesOf(a1_r).contains(a1_h))

        // B1 chain
        val b1_c = VisibilityNode(b1, ActionStep.COMMIT)
        val b1_h = VisibilityNode(b1, ActionStep.CHOOSE)
        val b1_r = VisibilityNode(b1, ActionStep.REVEAL)

        assertTrue(vg.dag.prerequisitesOf(b1_h).contains(b1_c))
        assertTrue(vg.dag.prerequisitesOf(b1_r).contains(b1_h))

        // Cross dependency: A1 is PUBLIC, so A1_CHOOSE -> B1_COMMIT
        assertTrue(vg.dag.prerequisitesOf(b1_c).contains(a1_h))
    }

    @Test
    fun `test hidden commit dependency`() {
        val a1 = alice to 1
        val b1 = bob to 1

        // A1 (Commit) -> B1
        val dag = createDag(
            actions = setOf(a1, b1),
            deps = mapOf(b1 to setOf(a1)),
            owners = mapOf(a1 to alice, b1 to bob),
            visibilities = mapOf(a1 to Visibility.COMMIT, b1 to Visibility.PUBLIC)
        )

        val vg = VisibilityGraphBuilder.build(dag)

        val a1_c = VisibilityNode(a1, ActionStep.COMMIT)
        val b1_c = VisibilityNode(b1, ActionStep.COMMIT)

        // A1 is COMMIT, so A1_COMMIT -> B1_COMMIT
        assertTrue(vg.dag.prerequisitesOf(b1_c).contains(a1_c))
    }
}

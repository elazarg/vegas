package vegas.ir

import vegas.RoleId
import vegas.FieldRef
import vegas.dag.Dag
import vegas.dag.ExplicitDag
import vegas.dag.Algo

/**
 * ActionId uniquely identifies an action in the game.
 * Pair of (role, stepIndex) where stepIndex is the phase index from IR.
 */
typealias ActionId = Pair<RoleId, Int>

/**
 * Metadata for each action: who performs it, what fields it writes,
 * visibility of those fields, and what fields are read in guards.
 */
data class ActionMetadata(
    val role: RoleId,
    val writes: Set<FieldRef>,            // fields written/introduced
    val visibility: Map<FieldRef, Visibility>,
    val guardReads: Set<FieldRef>         // fields read in guards/where
)

/**
 * Visibility determines how a field's value is revealed.
 * COMMIT: hidden committed value
 * REVEAL: reveals committed value
 * PUBLIC: plain public value, no prior commit
 */
enum class Visibility { COMMIT, REVEAL, PUBLIC }

/**
 * ActionDag is a specialized dependency DAG over ActionId with metadata.
 *
 * It wraps a generic Dag<ActionId> and adds action-specific queries
 * about roles, writes, visibility, and guard reads.
 *
 * Construction validates:
 * - Acyclicity
 * - Commit->Reveal ordering
 * - Visibility constraints on reads
 */
class ActionDag private constructor(
    private val underlying: Dag<ActionId>,
    private val meta: Map<ActionId, ActionMetadata>
) : Dag<ActionId> by underlying {

    fun metadata(a: ActionId): ActionMetadata = meta[a]
        ?: error("No metadata for action $a")

    fun owner(a: ActionId): RoleId = metadata(a).role
    fun writes(a: ActionId): Set<FieldRef> = metadata(a).writes
    fun visibility(a: ActionId): Map<FieldRef, Visibility> = metadata(a).visibility
    fun guardReads(a: ActionId): Set<FieldRef> = metadata(a).guardReads

    /**
     * Returns true if actions a and b can execute concurrently
     * (neither is reachable from the other).
     */
    fun canExecuteConcurrently(a: ActionId, b: ActionId): Boolean =
        !reaches(a, b) && !reaches(b, a)

    /**
     * Helper: check if there's a path from u to v in the DAG.
     */
    private fun reaches(u: ActionId, v: ActionId): Boolean =
        Algo.reaches(u, v, ::prerequisitesOf)

    companion object {
        /**
         * Build an ActionDag from nodes, prerequisites, and metadata.
         * Returns null if:
         * - Graph has cycles
         * - Commit->Reveal ordering is violated
         * - Actions read fields that aren't visible
         */
        fun from(
            nodes: Set<ActionId>,
            prerequisitesOf: (ActionId) -> Set<ActionId>,
            metadata: (ActionId) -> ActionMetadata
        ): ActionDag? {
            // Build underlying DAG (validates acyclicity)
            // ExplicitDag.from() throws on cycles, so catch and return null
            val dag = try {
                ExplicitDag.from(nodes, prerequisitesOf, checkAcyclic = true)
            } catch (e: IllegalArgumentException) {
                return null  // Cycle detected
            }

            val metaMap = nodes.associateWith(metadata)

            // Validate commit-reveal ordering
            if (!checkCommitRevealOrdering(dag, metaMap)) return null

            // Validate visibility on reads
            if (!checkVisibilityOnReads(dag, metaMap)) return null

            return ActionDag(dag, metaMap)
        }
    }
}

/**
 * Check that for each field with both COMMIT and REVEAL actions,
 * at least one commit reaches each reveal.
 */
private fun checkCommitRevealOrdering(
    dag: Dag<ActionId>,
    meta: Map<ActionId, ActionMetadata>
): Boolean {
    val commitsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()
    val revealsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()

    for ((a, m) in meta) {
        m.visibility.forEach { (field, vis) ->
            when (vis) {
                Visibility.COMMIT -> commitsByField.getOrPut(field) { mutableListOf() }.add(a)
                Visibility.REVEAL -> revealsByField.getOrPut(field) { mutableListOf() }.add(a)
                Visibility.PUBLIC -> {}
            }
        }
    }

    for ((field, reveals) in revealsByField) {
        val commits = commitsByField[field] ?: continue // no commit for this field; may be allowed elsewhere
        for (r in reveals) {
            // At least one commit must reach this reveal
            val ok = commits.any { c -> Algo.reaches(c, r, dag::prerequisitesOf) }
            if (!ok) return false
        }
    }
    return true
}

/**
 * Check that actions only read fields that are PUBLIC or REVEALed
 * by some predecessor.
 */
private fun checkVisibilityOnReads(
    dag: Dag<ActionId>,
    meta: Map<ActionId, ActionMetadata>
): Boolean {
    for ((a, m) in meta) {
        for (field in m.guardReads) {
            // Check if some predecessor b makes field visible
            val ok = meta.any { (b, mb) ->
                // b is a predecessor of a
                Algo.reaches(b, a, dag::prerequisitesOf) &&
                // and b makes field visible (PUBLIC or REVEAL)
                when (mb.visibility[field]) {
                    Visibility.PUBLIC, Visibility.REVEAL -> true
                    else -> false
                }
            }
            if (!ok) return false
        }
    }
    return true
}

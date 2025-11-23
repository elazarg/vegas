package vegas.ir

import vegas.RoleId
import vegas.FieldRef
import vegas.dag.Dag
import vegas.dag.ExplicitDag
import vegas.dag.DagSlice
import vegas.dag.Reachability
import vegas.dag.computeReachability

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
    private val meta: Map<ActionId, ActionMetadata>,
    private val reach: Reachability<ActionId>
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
        !reach.comparable(a, b)

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
            } catch (_: IllegalArgumentException) {
                return null  // Cycle detected
            }

            val metaMap = dag.nodes.associateWith(metadata)
            val slice = DagSlice(
                dag.nodes,
                dag.nodes.associateWith(dag::prerequisitesOf)
            )
            val reach = computeReachability(slice)
            // Validate commit-reveal ordering
            if (!checkCommitRevealOrdering(metaMap, reach)) return null

            // Validate visibility on reads
            if (!checkVisibilityOnReads(metaMap, reach)) return null

            return ActionDag(dag, metaMap, reach)
        }
    }
}

/**
 * Check that for each field with both COMMIT and REVEAL actions,
 * at least one commit reaches each reveal.
 */
private fun checkCommitRevealOrdering(
    meta: Map<ActionId, ActionMetadata>,
    reach: Reachability<ActionId>
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
            val ok = commits.any { c -> reach.reaches(c, r) }
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
    meta: Map<ActionId, ActionMetadata>,
    reach: Reachability<ActionId>
): Boolean {
    for ((a, m) in meta) {
        for (field in m.guardReads) {
            // Check if some predecessor b makes field visible
            val ok = meta.any { (b, mb) ->
                // b is a predecessor of a
                reach.reaches(b, a) &&
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

/**
 * Build an ActionDag from GameIR.
 *
 * Returns null if the IR has invalid dependency structure
 * (cycles, commit-reveal violations, or visibility violations).
 */
fun buildActionDag(ir: GameIR): ActionDag? {
    // Collect all actions
    val nodes = mutableSetOf<ActionId>()
    for ((phaseIdx, phase) in ir.phases.withIndex()) {
        for (role in phase.roles()) {
            nodes.add(role to phaseIdx)
        }
    }

    // Build dependencies
    val deps = mutableMapOf<ActionId, MutableSet<ActionId>>()

    for ((phaseIdx, phase) in ir.phases.withIndex()) {
        for ((role, sig) in phase.actions) {
            val actionId = role to phaseIdx
            val actionDeps = deps.getOrPut(actionId) { mutableSetOf() }

            // Add dependencies from guard reads
            for (capturedField in sig.requires.captures) {
                // Find the latest action before this one that writes this field
                val writer = findLatestWriter(capturedField, phaseIdx, ir)
                if (writer != null) {
                    actionDeps.add(writer)
                }
            }

            // Add commit->reveal dependencies
            for (param in sig.parameters) {
                val field = FieldRef(role, param.name)
                if (param.visible) {
                    // This might be a reveal - find prior commit
                    val priorCommit = findPriorCommit(field, phaseIdx, ir)
                    if (priorCommit != null) {
                        actionDeps.add(priorCommit)
                    }
                }
            }
        }
    }

    // Build metadata
    fun buildMetadata(actionId: ActionId): ActionMetadata {
        val (role, phaseIdx) = actionId
        val sig = ir.phases[phaseIdx].actions[role]!!

        val writes = sig.parameters.map { FieldRef(role, it.name) }.toSet()
        // Exclude fields being written in this action from guardReads
        // (they represent constraints on the values being written, not reads of prior values)
        val guardReads = sig.requires.captures - writes

        // Determine visibility for each written field
        val visibility = mutableMapOf<FieldRef, Visibility>()
        for (param in sig.parameters) {
            val field = FieldRef(role, param.name)
            val vis = determineVisibility(field, phaseIdx, param.visible, ir)
            visibility[field] = vis
        }

        return ActionMetadata(
            role = role,
            writes = writes,
            visibility = visibility,
            guardReads = guardReads
        )
    }

    return ActionDag.from(
        nodes = nodes,
        prerequisitesOf = { deps[it].orEmpty() },
        metadata = ::buildMetadata
    )
}

/**
 * Find the latest action before phaseIdx that writes the given field.
 */
private fun findLatestWriter(field: FieldRef, beforePhase: Int, ir: GameIR): ActionId? {
    for (phaseIdx in (beforePhase - 1) downTo 0) {
        val sig = ir.phases[phaseIdx].actions[field.role]
        if (sig != null && sig.parameters.any { it.name == field.param }) {
            return field.role to phaseIdx
        }
    }
    return null
}

/**
 * Find prior commit for a field (if this is a reveal).
 */
private fun findPriorCommit(field: FieldRef, beforePhase: Int, ir: GameIR): ActionId? {
    for (phaseIdx in (beforePhase - 1) downTo 0) {
        val sig = ir.phases[phaseIdx].actions[field.role]
        if (sig != null) {
            val param = sig.parameters.find { it.name == field.param }
            if (param != null && !param.visible) {
                // Found a commit (invisible parameter)
                return field.role to phaseIdx
            }
        }
    }
    return null
}

/**
 * Determine visibility for a field write.
 * - COMMIT: invisible parameter with no prior commit
 * - REVEAL: visible parameter with prior commit
 * - PUBLIC: visible parameter with no prior commit
 */
private fun determineVisibility(
    field: FieldRef,
    phaseIdx: Int,
    visible: Boolean,
    ir: GameIR
): Visibility {
    if (!visible) {
        return Visibility.COMMIT
    }

    // Check if there's a prior commit
    val priorCommit = findPriorCommit(field, phaseIdx, ir)
    return if (priorCommit != null) {
        Visibility.REVEAL
    } else {
        Visibility.PUBLIC
    }
}

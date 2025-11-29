package vegas.ir

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef
import vegas.dag.Dag
import vegas.dag.ExplicitDag
import vegas.dag.DagSlice
import vegas.dag.Reachability
import vegas.dag.computeReachability

typealias ActionId = Pair<RoleId, Int>

/**
 * High-level classification of an action’s kind.
 *
 * This is *derived* from:
 *  - whether this is a join step (join != null), and
 *  - how each written field is classified (Visibility).
 */
enum class ActionKind {
    COMMIT,
    REVEAL,
    YIELD,
}

/**
 * Visibility of a write to a field:
 *
 *  - COMMIT : hidden write (visible=false), with no prior commit
 *  - REVEAL : visible write with prior commit
 *  - PUBLIC : visible write with no prior commit
 *
 * Visibility is structural and determined purely by IR-level hidden/visible
 * flags plus commit/reveal ordering.
 */
enum class Visibility {
    COMMIT,
    REVEAL,
    PUBLIC,
}

/**
 * The reduced parameter info actually needed by backends.
 *
 * Structural visibility (commit / reveal / public) is *not* stored here;
 * it lives in [ActionStruct].
 */
data class ActionParam(
    val name: VarId,
    val type: Type,
)

/**
 * The semantic payload of an action: everything derived from [Signature] that
 * backends still need:
 *
 *  - params    : parameter list (name/type) in call order
 *  - join      : deposit info (if any); non-null iff this is the join step
 *  - guardExpr : the logical "where" expression that must hold
 */
data class ActionSpec(
    val params: List<ActionParam>,
    val join: Join?,       // non-null iff this is the join step
    val guardExpr: Expr,
)

/**
 * Structural metadata extracted from [Signature] and dependency analysis:
 *
 *  - role        : who performs the action
 *  - writes      : which fields are written
 *  - visibility  : visibility classification for each write
 *  - guardReads  : which fields the guard depends on
 *
 * This is the canonical location of commit/reveal/public semantics.
 */
data class ActionStruct(
    val role: RoleId,
    val writes: Set<FieldRef>,
    val visibility: Map<FieldRef, Visibility>,
    val guardReads: Set<FieldRef>,
) {
    /** Fields committed (hidden writes). */
    val commitFields: Set<FieldRef> by lazy {
        visibility.filterValues { it == Visibility.COMMIT }.keys
    }

    /** Fields revealed (clear writes with prior commit). */
    val revealFields: Set<FieldRef> by lazy {
        visibility.filterValues { it == Visibility.REVEAL }.keys
    }

    /** Fields written purely publicly (no commit/reveal). */
    val publicFields: Set<FieldRef> by lazy {
        visibility.filterValues { it == Visibility.PUBLIC }.keys
    }
}

/**
 * Full per-action payload that backends consume.
 *
 *  - id     : stable identifier within the DAG
 *  - spec   : semantic payload (params, join, guard)
 *  - struct : structural metadata (role, writes, visibility, guard reads)
 *
 * [kind] is derived from [spec] and [struct].
 */
data class ActionMeta(
    val id: ActionId,
    val spec: ActionSpec,
    val struct: ActionStruct,
) {
    val kind: ActionKind by lazy { inferKind(struct) }
}

/**
 * A DAG of actions equipped with per-node metadata.
 *
 * The underlying graph encodes causality / dependency between actions.
 * The payload map encodes, for each action:
 *  - who performs it,
 *  - what it reads,
 *  - what it writes,
 *  - its commit/reveal/public classification,
 *  - its guard expression.
 *
 * Reachability is precomputed for fast dependency and concurrency queries.
 */
class ActionDag private constructor(
    private val dag: Dag<ActionId>,
    private val payloads: Map<ActionId, ActionMeta>,
    private val reach: Reachability<ActionId>,
) : Dag<ActionId> by dag {

    /** All actions present in this DAG. */
    val actions: Set<ActionId> get() = payloads.keys

    /** All metadata objects, in no particular order. */
    val metas: Collection<ActionMeta> get() = payloads.values

    /** Metadata for a given action (throws if missing). */
    fun meta(id: ActionId): ActionMeta = payloads.getValue(id)

    /** Semantic shortcuts. */
    fun spec(id: ActionId): ActionSpec = meta(id).spec
    fun kind(id: ActionId): ActionKind = meta(id).kind
    fun params(id: ActionId): List<ActionParam> = meta(id).spec.params

    /** Structural shortcuts. */
    fun struct(id: ActionId): ActionStruct = meta(id).struct
    fun owner(id: ActionId): RoleId = struct(id).role
    fun visibilityOf(id: ActionId): Map<FieldRef, Visibility> = struct(id).visibility

    /** Reachability queries. */
    fun reaches(from: ActionId, to: ActionId): Boolean =
        reach.reaches(from, to)

    /**
     * Concurrency test: two nodes can execute concurrently iff neither reaches the other.
     */
    fun canExecuteConcurrently(a: ActionId, b: ActionId): Boolean =
        !reach.comparable(a, b)

    companion object {


        fun fromGraph(
            nodes: Set<ActionId>,
            deps: Map<ActionId, Set<ActionId>>,
            payloads: Map<ActionId, ActionMeta>,
        ): ActionDag? {
            val dag = ExplicitDag.from(
                nodes,
                prerequisitesOf = { n -> deps[n].orEmpty() },
                checkAcyclic = true,
            ) ?: return null

            val reach = computeReachability(dag.sliceFrom(nodes) as DagSlice<ActionId>)

            // Reuse the existing validators – they only depend on reach+payloads
            if (!validateCommitRevealOrdering(reach, payloads)) return null
            if (!validateVisibilityOnReads(reach, payloads)) return null

            return ActionDag(dag = dag, payloads = payloads, reach = reach)
        }

        fun expandCommitReveal(dag: ActionDag): ActionDag {
            // 1. Identify pure-public actions
            val purePublic: Set<ActionId> = dag.actions.filter { id ->
                val s = dag.struct(id)
                s.commitFields.isEmpty() && s.revealFields.isEmpty() && s.publicFields.isNotEmpty()
            }.toSet()

            // 2. Build Risk and Split sets
            val riskPartners = mutableMapOf<ActionId, MutableSet<ActionId>>()
            for (a in purePublic) {
                for (b in purePublic) {
                    if (a == b) continue
                    if (dag.canExecuteConcurrently(a, b)) {
                        riskPartners.getOrPut(a) { mutableSetOf() }.add(b)
                    }
                }
            }

            val split: Set<ActionId> = riskPartners.filterValues { it.isNotEmpty() }.keys

            // Nothing concurrent, so nothing to do
            if (split.isEmpty()) return dag

            // 3. Allocate fresh ids for commit/reveal nodes
            val commitId = mutableMapOf<ActionId, ActionId>()
            val revealId = mutableMapOf<ActionId, ActionId>()

            // Simple strategy: keep role, use fresh integer index above current max
            val maxIndex = dag.actions.maxOf { it.second }
            var nextIndex = maxIndex + 1

            fun freshCommitId(base: ActionId): ActionId {
                val id: ActionId = base.first to nextIndex++
                commitId[base] = id
                return id
            }

            fun freshRevealId(base: ActionId): ActionId {
                val id: ActionId = base.first to nextIndex++
                revealId[base] = id
                return id
            }

            // Pre-create ids for all split actions
            for (id in split) {
                freshCommitId(id)
                freshRevealId(id)
            }

            // 4. New metadata and predecessor map
            val newMetas = mutableMapOf<ActionId, ActionMeta>()
            val newPreds = mutableMapOf<ActionId, MutableSet<ActionId>>()

            // Helper: map a predecessor from old graph to new graph
            fun mapPred(old: ActionId): ActionId =
                if (old in split) revealId.getValue(old) else old

            // 4a. Copy non-split nodes
            for (id in dag.actions) {
                if (id in split) continue
                val meta = dag.meta(id)
                val mappedPreds = dag.prerequisitesOf(id).mapTo(mutableSetOf()) { p -> mapPred(p) }
                newMetas[id] = meta
                newPreds[id] = mappedPreds
            }

            // 4b. Create commit + reveal nodes for split actions
            for (a in split) {
                val meta = dag.meta(a)
                val struct = meta.struct
                val spec = meta.spec

                val cid = commitId.getValue(a)
                val rid = revealId.getValue(a)

                // Commit struct: public writes become COMMIT
                val commitVis = struct.visibility.mapValues { (_, vis) ->
                    if (vis == Visibility.PUBLIC) Visibility.COMMIT else vis
                }
                val commitStruct = struct.copy(visibility = commitVis)

                // Reveal struct: public writes become REVEAL
                val revealVis = struct.visibility.mapValues { (_, vis) ->
                    if (vis == Visibility.PUBLIC) Visibility.REVEAL else vis
                }
                val revealStruct = struct.copy(visibility = revealVis)

                // Commit spec:
                //  - KEEP join (deposit happens at commit time)
                //  - trivial guard (always allowed to commit)
                val commitSpec = spec.copy(
                    join = spec.join,
                    guardExpr = Expr.Const.BoolVal(true)
                )

                // Reveal spec:
                //  - original guard
                //  - NO join (deposit already done)
                val revealSpec = spec.copy(
                    join = null,
                    guardExpr = spec.guardExpr
                )

                val commitMeta = ActionMeta(
                    id = cid,
                    spec = commitSpec,
                    struct = commitStruct
                )

                val revealMeta = ActionMeta(
                    id = rid,
                    spec = revealSpec,
                    struct = revealStruct
                )

                // Commit predecessors: mapped original preds
                val commitPreds = dag.prerequisitesOf(a).mapTo(mutableSetOf()) { p -> mapPred(p) }

                // Reveal predecessors:
                val revealPreds = mutableSetOf<ActionId>()
                // original deps (through commit)
                revealPreds.addAll(commitPreds)
                // must commit itself
                revealPreds.add(cid)
                // must wait for all partners' commits
                val partners = riskPartners[a].orEmpty()
                for (b in partners) {
                    val bCommit = commitId.getValue(b)
                    revealPreds.add(bCommit)
                }

                newMetas[cid] = commitMeta
                newMetas[rid] = revealMeta
                newPreds[cid] = commitPreds
                newPreds[rid] = revealPreds
            }

            // 5. Build new underlying DAG and reachability
            val newNodes: Set<ActionId> = newMetas.keys

            val newUnderlying: Dag<ActionId> =
                ExplicitDag.from(
                    newNodes,
                    prerequisitesOf = { n -> newPreds[n].orEmpty() },
                    checkAcyclic = true
                ) ?: error("expandCommitReveal produced a cyclic graph")

            val slice = newUnderlying.sliceFrom(newNodes) as DagSlice<ActionId>
            val newReach = computeReachability(slice)

            return ActionDag(
                dag = newUnderlying,
                payloads = newMetas,
                reach = newReach
            )
        }
    }
}

/* -------------------------------------------------------------------------- */
/*  Kind inference                                                            */
/* -------------------------------------------------------------------------- */

private fun inferKind(
    struct: ActionStruct,
): ActionKind {
    val hasCommit = struct.visibility.values.any { it == Visibility.COMMIT }
    val hasReveal = struct.visibility.values.any { it == Visibility.REVEAL }

    return when {
        hasCommit && !hasReveal -> ActionKind.COMMIT
        hasReveal && !hasCommit -> ActionKind.REVEAL
        else -> ActionKind.YIELD   // includes pure join steps
    }
}


/**
 * Ensure that for every REVEAL write, there exists a prior COMMIT write to
 * the same field on some path in the DAG.
 */
private fun validateCommitRevealOrdering(
    reach: Reachability<ActionId>,
    payloads: Map<ActionId, ActionMeta>,
): Boolean {
    val commitsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()
    val revealsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()

    for ((id, meta) in payloads) {
        for ((f, vis) in meta.struct.visibility) {
            when (vis) {
                Visibility.COMMIT -> commitsByField.getOrPut(f) { mutableListOf() }.add(id)
                Visibility.REVEAL -> revealsByField.getOrPut(f) { mutableListOf() }.add(id)
                Visibility.PUBLIC -> {}
            }
        }
    }

    for ((field, reveals) in revealsByField) {
        val commits = commitsByField[field].orEmpty()
        if (commits.isEmpty()) return false

        for (rev in reveals) {
            val ok = commits.any { com -> reach.reaches(com, rev) }
            if (!ok) return false
        }
    }

    return true
}

/**
 * Ensure that whenever a guard reads a field, that field is already visible
 * (PUBLIC or REVEAL) at or before that action.
 */
private fun validateVisibilityOnReads(
    reach: Reachability<ActionId>,
    payloads: Map<ActionId, ActionMeta>,
): Boolean {
    // Points where each field becomes visible (PUBLIC or REVEAL)
    val visPoints = mutableMapOf<FieldRef, MutableList<ActionId>>()
    val commitPoints = mutableMapOf<FieldRef, MutableList<ActionId>>()
    for ((id, meta) in payloads) {
        for ((field, vis) in meta.struct.visibility) {
            if (vis == Visibility.PUBLIC || vis == Visibility.REVEAL) {
                visPoints.getOrPut(field) { mutableListOf() }.add(id)
            }
            if (vis == Visibility.COMMIT) {
                commitPoints.getOrPut(field) { mutableListOf() }.add(id)
            }
        }
    }

    for ((id, meta) in payloads) {
        for (f in meta.struct.guardReads) {
            val points = visPoints[f].orEmpty()

            // Field must be visible at or before this action
            val visibleOk = points.any { v -> v == id || reach.reaches(v, id) }
            val selfCommitOk = if (f.role == meta.struct.role) {
                commitPoints[f].orEmpty().any { c -> c == id || reach.reaches(c, id) }
            } else false

            val ok = visibleOk || selfCommitOk
            if (!ok) return false
        }
    }
    return true
}

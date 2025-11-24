package vegas.ir

import vegas.FieldRef
import vegas.RoleId
import vegas.frontend.Phase

/** Where a (role,var) appears, and whether it’s commit or reveal. */
data class Occurrence(val phase: Int, val visible: Boolean)

data class Index(
    val phases: List<Phase>,
    val pos: Map<FieldRef, List<Occurrence>>,      // all appearances (ordered by phase)
    val firstCommitPhase: Map<FieldRef, Int?>,      // null if never committed (first occurrence is public)
    val firstRevealPhase: Map<FieldRef, Int?>       // null if never revealed (stays hidden)
)

fun buildIndex(g: GameIR): Index {
    val pos = mutableMapOf<FieldRef, MutableList<Occurrence>>()
    g.phases.forEachIndexed { pi, phase ->
        phase.actions.forEach { (role, sig) ->
            sig.parameters.forEach { p ->
                pos.getOrPut(FieldRef(role, p.name)) { mutableListOf() }
                    .add(Occurrence(pi, p.visible))
            }
        }
    }
    // compute first commit (visible=false) and first later reveal (visible=true after a commit)
    val firstCommit = mutableMapOf<FieldRef, Int?>()
    val firstReveal = mutableMapOf<FieldRef, Int?>()
    pos.forEach { (k, occs) ->
        val firstC = occs.indexOfFirst { !it.visible }.takeIf { it >= 0 }?.let { occs[it].phase }
        firstCommit[k] = firstC
        val rev = if (firstC != null) occs.firstOrNull { it.phase > firstC && it.visible }?.phase else null
        firstReveal[k] = rev
    }
    return Index(g.phases, pos.mapValues { it.value.toList() }, firstCommit, firstReveal)
}

/** Snapshot legality: guard can be checked at phase k iff it doesn’t read same-phase or unrevealed-hidden. */
data class GuardSplit(val checkNow: Expr, val checkLater: Expr?)

fun splitGuardForPhase(sig: Signature, role: RoleId, phaseIdx: Int, idx: Index): GuardSplit {
    val refs = sig.requires.captures
    val usesSamePhase = refs.any { r ->
        idx.pos[FieldRef(r.role, r.param)]?.any { it.phase == phaseIdx } == true
    }
    val usesUnrevealedHidden = refs.any { r ->
        val k = FieldRef(r.role, r.param)
        val c = idx.firstCommitPhase[k]
        val rev = idx.firstRevealPhase[k]
        // If committed and not revealed yet by phaseIdx, it’s unrevealed
        c != null && (rev == null || rev > phaseIdx)
    }
    val decidable = !(usesSamePhase || usesUnrevealedHidden)
    return if (decidable) GuardSplit(sig.requires.condition, null)
    else GuardSplit(Expr.BoolVal(true), sig.requires.condition)
}

/** Domain guard for SetType (reused at public set or reveal). */
fun domainGuard(param: Parameter, field: FieldRef): Expr? =
    when (param.type) {
        is Type.SetType -> {
            val tests = param.type.values.map { Expr.Eq(Expr.Field(field), Expr.IntVal(it)) }
            tests.reduceOrNull<Expr, Expr> { acc, e -> Expr.Or(acc, e) }
        }
        is Type.IntType, is Type.BoolType -> null
    }

/** Well-formedness checks (sketch) */
sealed class WF {
    data class SamePhaseRead(val role: RoleId, val phase: Int, val field: FieldRef): WF()
    data class RevealBeforeCommit(val key: FieldRef, val phase: Int): WF()
    data class DuplicateInPhase(val key: FieldRef, val phase: Int): WF()
    data class UnrevealedUsedInPayoff(val key: FieldRef): WF()
    data class NonFieldRefSetValue(val key: FieldRef): WF() // optional: static if you carry literal-only domains
}

fun checkWellFormed(g: GameIR): List<WF> {
    val idx = buildIndex(g)
    val errs = mutableListOf<WF>()

    // 1) no duplicate param per role per phase
    g.phases.forEachIndexed { pi, phase ->
        val seen = mutableSetOf<FieldRef>()
        phase.actions.forEach { (r, sig) ->
            sig.parameters.forEach { p ->
                val key = FieldRef(r, p.name)
                if (!seen.add(key)) errs += WF.DuplicateInPhase(key, pi)
            }
        }
    }

    // 2) no reveal before commit (first visible=true after some visible=false)
    idx.pos.forEach { (k, occs) ->
        val firstC = idx.firstCommitPhase[k] ?: return@forEach
        // no commit; all occurrences are public declarations
        val firstV = occs.firstOrNull { it.visible }?.phase
        if (firstV != null && firstV <= firstC) errs += WF.RevealBeforeCommit(k, firstV)
    }

    // 3) guards’ captures only from earlier phases
    g.phases.forEachIndexed { pi, phase ->
        phase.actions.forEach { (r, sig) ->
            sig.requires.captures.forEach { f ->
                val occs = idx.pos[FieldRef(f.role, f.param)] ?: emptyList()
                if (occs.any { it.phase == pi }) errs += WF.SamePhaseRead(r, pi, f)
            }
        }
    }

    // 4) payoffs only read fields that end up public/revealed by terminal
    val lastPhase = g.phases.lastIndex
    g.payoffs.values.forEach { e ->
        collectFieldRefs(e).forEach { f ->
            val k = FieldRef(f.role, f.param)
            val c = idx.firstCommitPhase[k]
            val rev = idx.firstRevealPhase[k]
            val definedByEnd = when {
                c == null -> true                // was public at some phase (by definition)
                rev != null && rev <= lastPhase -> true
                else -> false
            }
            if (!definedByEnd) errs += WF.UnrevealedUsedInPayoff(k)
        }
    }

    return errs
}

/** Utility: collect FieldRef refs in an Expr (for payoffs or custom checks). */
fun collectFieldRefs(e: Expr): Set<FieldRef> {
    val out = linkedSetOf<FieldRef>()
    fun go(x: Expr) {
        when (x) {
            is Expr.Field -> out += x.field
            is Expr.IsDefined -> out += x.field
            is Expr.IntVal, is Expr.BoolVal -> {}
            is Expr.Add -> { go(x.l); go(x.r) }
            is Expr.Sub -> { go(x.l); go(x.r) }
            is Expr.Mul -> { go(x.l); go(x.r) }
            is Expr.Div -> { go(x.l); go(x.r) }
            is Expr.Neg -> go(x.x)
            is Expr.Eq  -> { go(x.l); go(x.r) }
            is Expr.Ne  -> { go(x.l); go(x.r) }
            is Expr.Lt  -> { go(x.l); go(x.r) }
            is Expr.Le  -> { go(x.l); go(x.r) }
            is Expr.Gt  -> { go(x.l); go(x.r) }
            is Expr.Ge  -> { go(x.l); go(x.r) }
            is Expr.And -> { go(x.l); go(x.r) }
            is Expr.Or  -> { go(x.l); go(x.r) }
            is Expr.Not -> go(x.x)
            is Expr.Ite -> { go(x.c); go(x.t); go(x.e) }
        }
    }
    go(e); return out
}

package vegas.ir

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId


// ---------------- Naming helpers ----------------
private fun pidPhaseOpen(i: Int) = PlaceId("phase[$i]:open")
private fun pidRoleDone(i: Int, r: RoleId) = PlaceId("phase[$i]:${r.name}:done")
private fun pidFieldDone(r: RoleId, v: VarId) = PlaceId("field[${r.name}.${v.name}]:done")

private fun tidAct(i: Int, r: RoleId) = TransId("t[$i]:${r.name}:act")
private fun tidPhaseComplete(i: Int) = TransId("t[$i]:complete")

// ---------------- IR -> Petri translation ----------------
/**
 * Construct a 1-safe workflow Petri net from a straight-line phased GameIR.
 *
 * Semantics:
 *  - Each phase i has a control place phase[i]:open. The initial marking holds a token in phase[0]:open.
 *  - Each role r in phase i has a single atomic transition t[i]:r:act guarded by the role's Requirement.condition.
 *  - Firing t[i]:r:act marks all (r,param) fields as defined (MarkDefined + post arc to field[r.param]:done)
 *    and also marks phase-local completion place phase[i]:r:done.
 *  - A phase-completion transition t[i]:complete requires all phase[i]:r:done and phase[i]:open and opens phase[i+1]:open.
 *
 * Notes:
 *  - Data dependencies (Requirement.captures) are honored downstream when lowering guards/IsDefined; they need no explicit arcs here
 *    because ExprGuard already refers to FieldRef(IsDefined ...) whose truth reflects whether field[r.param]:done has been produced.
 */
fun irToPetri(g: GameIR): PNSystem {
    val places = linkedSetOf<Place>()
    val trans = linkedSetOf<TransId>()
    val pre = linkedSetOf<ArcPT>()
    val post = linkedSetOf<ArcTP>()
    val ann = linkedMapOf<TransId, TransitionAnn>()

    // Create phase-open places
    val phaseOpenPlaces = (g.phases.indices).associateWith { i ->
        val p = pidPhaseOpen(i)
        places += Place(p)
        p
    }

    // Initial marking: phase 0 open (if there is at least one phase)
    val init = mutableSetOf<PlaceId>()
    if (g.phases.isNotEmpty()) init += phaseOpenPlaces.getValue(0)

    // For each phase, create role actions and a phase-complete synchronizer
    for ((i, phase) in g.phases.withIndex()) {
        val openP = phaseOpenPlaces.getValue(i)

        // Per-role action transitions
        val roleDonePlaces = mutableListOf<PlaceId>()
        for ((role, sig) in phase.actions) {
            val t = tidAct(i, role)
            trans += t
            // Pre: phase open
            pre += ArcPT(openP, t)

            // Post: mark role-done for this phase
            val doneP = pidRoleDone(i, role)
            places += Place(doneP)
            post += ArcTP(t, doneP)
            roleDonePlaces += doneP

            // Post: mark each field of this role as defined
            for (param in sig.parameters) {
                val fp = pidFieldDone(role, param.name)
                places += Place(fp)
                post += ArcTP(t, fp)
            }

            // Guard: the signature's requirement condition (symbolic)
            val guard = Guard.ExprGuard(sig.requires.condition)
            // Updates: symbolic declarations that fields became defined
            val updates = sig.parameters.map { Update.MarkDefined(FieldRef(role, it.name)) }
            ann[t] = TransitionAnn(t, guard, updates)
        }

        // Phase-completion transition to open next phase (if any)
        if (i + 1 < g.phases.size) {
            val tComplete = tidPhaseComplete(i)
            trans += tComplete

            // Need phase open AND all role-done
            pre += ArcPT(openP, tComplete)
            for (rp in roleDonePlaces) pre += ArcPT(rp, tComplete)

            val nextOpen = phaseOpenPlaces.getValue(i + 1)
            post += ArcTP(tComplete, nextOpen)

            // No extra places required beyond those already added; guard is True, no updates
            ann[tComplete] = TransitionAnn(tComplete, Guard.True, emptyList())
        }
    }

    val net = PetriNet(
        places = places,
        trans = trans,
        pre = pre,
        post = post
    )

    return PNSystem(net = net, ann = ann, init = init)
}

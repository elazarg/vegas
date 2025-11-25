package vegas.backend.scribble

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.GameIR
import vegas.frontend.Phase
import vegas.ir.Signature
import vegas.ir.Type

fun genScribbleFromIR(g: GameIR): String {
    val protocol = generateScribbleFromIR(g)
    return protocol.prettyPrintAll()
}

private fun generateScribbleFromIR(g: GameIR): Sast.Protocol {
    val types = mapOf(
        "int" to "Integer",
        "bool" to "Boolean"
    )

    val actions = phasesToScribble(g)

    return Sast.Protocol(
        name = g.name,
        types = types,
        roles = g.roles.toSet(),
        block = Sast.Block(actions)
    )
}

// ========== Phase to Scribble Actions ==========

private fun phasesToScribble(g: GameIR): List<Sast.Action> {
    throw NotImplementedError("Scribble backend not yet migrated to ActionDag")
}

private fun phaseToScribble(
    phase: Phase,
    phaseIdx: Int,
    history: Map<FieldRef, List<ParamOccurrence>>,
    allRoles: Set<RoleId>
): List<Sast.Action> {
    // Process signatures in consistent order (matches AST sortedBy rankOrder)
    return phase.actions.entries
        .flatMap { (role, sig) ->
            signatureToScribble(role, sig, phaseIdx, history, allRoles)
        }
        .sortedBy { rankOrder(it) }
}

private fun signatureToScribble(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    history: Map<FieldRef, List<ParamOccurrence>>,
    allRoles: Set<RoleId>
): List<Sast.Action> {
    val actions = mutableListOf<Sast.Action>()

    // Determine if this is a reveal
    val isReveal = sig.parameters.any { param ->
        val occurrences = history[FieldRef(role, param.name)] ?: emptyList()
        val priorCommit = occurrences.any { it.phase < phaseIdx && !it.visible }
        priorCommit && param.visible
    }

    // Connect action for joins
    if (sig.join != null) {
        actions.add(Sast.Action.Connect(role))
    }

    // Send actions
    if (isReveal) {
        // Reveal: send all parameters as "Reveal"
        val params = sig.parameters.map { param ->
            param.name.name to scribbleTypeOf(param.type)
        }
        actions.add(Sast.Action.Send("Reveal", params, role, setOf(SERVER)))
    } else {
        // Regular: split hidden/public
        val (hidden, public) = sig.parameters.partition { !it.visible }

        if (hidden.isNotEmpty()) {
            val params = hidden.map { param ->
                param.name.name to "hidden"
            }
            actions.add(Sast.Action.Send("Hidden", params, role, setOf(SERVER)))
        }

        if (public.isNotEmpty()) {
            val params = public.map { param ->
                param.name.name to scribbleTypeOf(param.type)
            }
            actions.add(Sast.Action.Send("Public", params, role, setOf(SERVER)))
        }
    }

    // Broadcast non-hidden parameters
    val broadcastParams = sig.parameters
        .filter { it.visible }
        .map { param -> param.name.name to scribbleTypeOf(param.type) }

    actions.add(Sast.Action.Send("Broadcast", broadcastParams, SERVER, allRoles - role))

    return actions
}

// ========== Parameter History Tracking ==========

private data class ParamOccurrence(val phase: Int, val visible: Boolean)

private fun buildParamHistory(g: GameIR): Map<FieldRef, List<ParamOccurrence>> {
    throw NotImplementedError("Scribble backend not yet migrated to ActionDag")
}

// ========== Utilities ==========

private fun rankOrder(action: Sast.Action): Int =
    if (action is Sast.Action.Send) {
        when (action.label) {
            "Hidden" -> 1
            "Reveal" -> 2
            else -> 3
        }
    } else 0

private fun scribbleTypeOf(t: Type): String = when (t) {
    Type.IntType -> "int"
    Type.BoolType -> "bool"
    is Type.SetType -> "int" // Sets represented as int in Scribble
}

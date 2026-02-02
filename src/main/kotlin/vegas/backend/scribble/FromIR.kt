package vegas.backend.scribble

import vegas.RoleId
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.ActionDag
import vegas.ir.ActionMeta
import vegas.ir.Visibility

fun genScribbleFromIR(g: GameIR): String {
    val protocol = generateScribbleFromIR(g)
    return protocol.prettyPrintAll()
}

private fun generateScribbleFromIR(g: GameIR): Sast.Protocol {
    val types = mapOf(
        "int" to "Integer",
        "bool" to "Boolean"
    )

    val actions = dagToScribble(g.dag, g.roles)

    return Sast.Protocol(
        name = g.name,
        types = types,
        roles = g.roles.toSet(),
        block = Sast.Block(actions)
    )
}

private fun dagToScribble(dag: ActionDag, allRoles: Set<RoleId>): List<Sast.Action> {
    // Use topological sort to ensure dependencies are respected (e.g. commit-reveal ordering)
    return dag.topo().flatMap { id ->
        actionToScribble(dag.meta(id), allRoles)
    }
}

private fun actionToScribble(meta: ActionMeta, allRoles: Set<RoleId>): List<Sast.Action> {
    val actions = mutableListOf<Sast.Action>()
    val role = meta.struct.owner

    // 1. Connect (Join)
    if (meta.spec.join != null) {
        actions.add(Sast.Action.Connect(role))
    }

    // 2. Send action
    // Map visibility to Scribble label
    val label = when (meta.kind) {
        Visibility.COMMIT -> "Hidden"
        Visibility.REVEAL -> "Reveal"
        Visibility.PUBLIC -> "Public"
    }

    val params = meta.spec.params.map { param ->
        val typeStr = if (meta.kind == Visibility.COMMIT) "hidden" else scribbleTypeOf(param.type)
        param.name.name to typeStr
    }

    // Always generate a Send action if there are parameters or if it's a commit (implying hidden info)
    // Or even if empty? Scribble actions usually have content or just signal.
    // If params is empty, we still send the label (e.g. reveal without params? maybe not possible in Vegas)
    if (params.isNotEmpty()) {
        actions.add(Sast.Action.Send(label, params, role, setOf(SERVER)))
    }

    // 3. Broadcast (if visible)
    if (meta.kind == Visibility.REVEAL || meta.kind == Visibility.PUBLIC) {
        val broadcastParams = meta.spec.params.map { param ->
            param.name.name to scribbleTypeOf(param.type)
        }
        val targets = allRoles - role
        if (broadcastParams.isNotEmpty() && targets.isNotEmpty()) {
             actions.add(Sast.Action.Send("Broadcast", broadcastParams, SERVER, targets))
        }
    }

    return actions
}

private fun scribbleTypeOf(t: Type): String = when (t) {
    Type.IntType -> "int"
    Type.BoolType -> "bool"
    is Type.RangeType -> "int" // Ranges represented as int in Scribble
}

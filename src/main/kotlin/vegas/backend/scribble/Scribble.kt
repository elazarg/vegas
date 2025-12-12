package vegas.backend.scribble


import vegas.RoleId
import vegas.join
import vegas.names
import vegas.types

sealed class Sast {
    data class Protocol(val name: String, val types: Map<String, String>, val roles: Set<RoleId>, val block: Block) :
        Sast()

    data class Block(val stmts: List<Action>) : Sast()

    sealed class Action : Sast() {
        data class Send(val label: String, val params: List<Pair<String, String>>, val from: RoleId, val to: Set<RoleId>?) :
            Action()

        data class Connect(val to: RoleId) : Action()
        data class Choice(val at: RoleId, val choices: List<Block>) : Action()
        data class Rec(val label: String, val actions: Block) : Action()
        data class Continue(val label: String) : Action()
    }

}

val SERVER = RoleId("Server")

fun Sast.Protocol.prettyPrintAll(): String {
    val typedecls = types.map { """type <java> "java.lang.${it.value}" from "rt.jar" as ${it.key};""" }.join("\n")
    val items = listOf("module Game;", typedecls, prettyPrint()) + (roles + SERVER).map { prettyPrint(it) }
    return items.join("\n\n")
}

fun Sast.prettyPrint(role: RoleId? = null, indent: Int = 0, connected: Set<RoleId> = setOf()): String {
    fun pretty(x: Sast) = x.prettyPrint(role, indent, connected)
    val code = when (this) {
        is Sast.Protocol -> {
            assert(indent == 0)
            val ps = roles.join(", ") { "role $it" }
            when (role) {
                null -> "explicit global protocol $name(role Server, $ps)"
                SERVER -> "local protocol ${name}_Server(role Server, $ps)"
                else -> "local protocol ${name}_$role(role Server, role $role)"
            } + pretty(block)
        }

        is Sast.Block -> stmts
            .map { it.prettyPrint(role, indent + 1, if (it is Sast.Action.Connect) connected + it.to else connected) }
            .filter { it.isNotBlank() }
            .joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n")

        is Sast.Action.Send -> {
            var res = if (params.isEmpty()) "$label()" else "${label}_${params.names().join("_")}(${
                params.types().join(", ")
            })"
            if (role == null || to == null || role in to)
                res += " from $from"
            if (to != null && (role == null || from == role))
                res += " to ${to.join(", ")}"
            if (" to " in res || " from " in res) res
            else ""
        }

        is Sast.Action.Connect ->
            when (role) {
                null -> "connect Server to $to"
                to -> "accept Server"
                else -> ""
            }

        is Sast.Action.Choice -> {
            val blocks = choices.join(" or ") { pretty(it) }
            "choice at $at $blocks"
        }

        is Sast.Action.Rec -> "rec " + pretty(actions)
        is Sast.Action.Continue -> "continue $label"
    }
    return "    ".repeat(indent) + code
}

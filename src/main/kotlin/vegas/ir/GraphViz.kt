package vegas.ir

import vegas.RoleId

/**
 * Render the GameIR as a Graphviz DOT string.
 */
fun GameIR.toGraphviz(): String =
    dag.toGraphviz(
        gameName   = name,
        chanceRoles = chanceRoles
    )

/**
 * Render an ActionDag as Graphviz DOT.
 */
fun ActionDag.toGraphviz(
    gameName: String = "ActionDag",
    chanceRoles: Set<RoleId> = emptySet(),
): String {
    val sb = StringBuilder()

    sb.appendLine("digraph \"${escapeId(gameName)}\" {")
    sb.appendLine("  rankdir=LR;")
    // Use a nicer font and orthogonal lines for a circuit-like look (optional)
    sb.appendLine("  node [fontname=\"Helvetica\", fontsize=10, style=filled, penwidth=0.5];")
    sb.appendLine("  edge [fontname=\"Helvetica\", fontsize=9, color=\"#555555\"];")
    sb.appendLine("  splines=true;") // Use 'ortho' for square lines, 'true' for curved

    // Group actions by owning role
    val byRole: Map<RoleId, List<ActionId>> =
        actions.groupBy { owner(it) }

    // Emit one cluster per role
    byRole.entries.sortedBy { it.key.toString() }.forEachIndexed { idx, (role, ids) ->
        sb.appendLine("  subgraph \"cluster_${idx}\" {")
        val isChance = role in chanceRoles
        val roleLabel = if (isChance) "${role.name} (Chance)" else role.name

        sb.appendLine("    label=\"${escapeLabel(roleLabel)}\";")
        sb.appendLine("    style=dashed;")
        sb.appendLine("    color=\"#777777\";") // Darker grey for cluster border
        sb.appendLine("    fontcolor=\"#333333\";")

        ids.sortedBy { it.second }.forEach { id ->
            val nodeName  = nodeId(id)
            // Pass the relative index (id.second) instead of full ID to save space
            val labelHtml = nodeHtmlLabel(id, id.second)

            // Determine attributes based on ActionKind and Role
            val kind = kind(id)
            val shape = if (isChance) "diamond" else "box"

            // Color Palette
            val fillColor = when(kind) {
                ActionKind.COMMIT -> "#FFD1DC" // Pastel Pink
                ActionKind.REVEAL -> "#C1E1C1" // Pastel Green
                ActionKind.YIELD  -> "#F0F0F0" // Light Grey
            }

            // Stylize the border slightly for Commits
            val penWidth = if (kind == ActionKind.COMMIT) "1.5" else "0.5"

            sb.appendLine(
                "    $nodeName [label=<$labelHtml>, shape=$shape, fillcolor=\"$fillColor\", penwidth=$penWidth];"
            )
        }

        sb.appendLine("  }")
    }

    // Emit edges
    actions.forEach { to ->
        prerequisitesOf(to).forEach { from ->
            sb.appendLine("  ${nodeId(from)} -> ${nodeId(to)};")
        }
    }

    sb.appendLine("}")
    return sb.toString()
}

/* -------------------------------------------------------------------------- */
/* Helpers                                                                   */
/* -------------------------------------------------------------------------- */

private fun ActionDag.nodeId(id: ActionId): String {
    val roleName = try { owner(id).name } catch (_: Throwable) { owner(id).toString() }
    val raw = "n_${roleName}_${id.second}"
    return "\"${escapeId(raw)}\""
}

/** * Generates an HTML-like label for Graphviz.
 * This allows mixing fonts, sizes, and layout within the node.
 */
private fun ActionDag.nodeHtmlLabel(id: ActionId, index: Int): String {
    val kind = kind(id)
    val params = params(id)

    // 1. Choose a Symbol/Icon
    val symbol = when(kind) {
        ActionKind.COMMIT -> "&#128274;" // 🔒 Lock
        ActionKind.REVEAL -> "&#128065;" // 👁 Eye
        ActionKind.YIELD  -> ""           // Clean, no icon for standard yield
    }

    // 2. Format the Parameter list
    val paramText = if (params.isNotEmpty()) {
        params.joinToString(", ") { "<b>${it.name.name}</b>" }
    } else {
        // If there are no params, and it's a yield, we might want a placeholder
        if (kind == ActionKind.YIELD) "" else ""
    }

    // 3. Build the Table-based Label
    // The top row is the ID (small), bottom row is Symbol + Params
    val sb = StringBuilder()
    sb.append("<table border=\"0\" cellborder=\"0\" cellspacing=\"0\">")

    // Row 1: The small index number (e.g., #3)
    sb.append("<tr><td><font point-size=\"8\" color=\"#555555\">#$index</font></td></tr>")

    // Row 2: The Action
    sb.append("<tr><td>")
    if (symbol.isNotEmpty()) {
        sb.append("<font point-size=\"14\">$symbol</font>")
    }
    if (symbol.isNotEmpty() && paramText.isNotEmpty()) {
        sb.append(" ") // Spacer
    }
    if (paramText.isNotEmpty()) {
        sb.append(paramText)
    }
    // If empty (plain yield with no params), add a subtle dot or dash
    if (symbol.isEmpty() && paramText.isEmpty()) {
        sb.append("<font color=\"#AAAAAA\">&#8212;</font>") // Em-dash
    }
    sb.append("</td></tr>")
    sb.append("</table>")

    return sb.toString()
}

private fun escapeId(s: String): String =
    s.replace("\\", "_").replace("\"", "_").replace("[^A-Za-z0-9_]+".toRegex(), "_")

private fun escapeLabel(s: String): String =
    s.replace("\\", "\\\\").replace("\"", "\\\"")

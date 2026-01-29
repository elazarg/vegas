/**
 * # MAID Backend: JSON Serialization
 *
 * Serializes MaidGame to JSON format compatible with Thrones game theory workbench.
 * Uses manual serialization to avoid external dependencies.
 */
package vegas.backend.maid

/**
 * Serialize a MaidGame to JSON string.
 *
 * @param game The MAID game to serialize
 * @param pretty Whether to format with indentation (default: true)
 * @return JSON string
 */
fun maidToJson(game: MaidGame, pretty: Boolean = true): String {
    val indent = if (pretty) "  " else ""
    val newline = if (pretty) "\n" else ""

    return buildString {
        append("{")
        append(newline)

        // id
        append(indent)
        append("\"id\": ")
        append(jsonString(game.id))
        append(",")
        append(newline)

        // title
        append(indent)
        append("\"title\": ")
        append(jsonString(game.title))
        append(",")
        append(newline)

        // description
        if (game.description != null) {
            append(indent)
            append("\"description\": ")
            append(jsonString(game.description))
            append(",")
            append(newline)
        }

        // format_name
        append(indent)
        append("\"format_name\": \"maid\",")
        append(newline)

        // agents
        append(indent)
        append("\"agents\": ")
        append(jsonStringList(game.agents))
        append(",")
        append(newline)

        // nodes
        append(indent)
        append("\"nodes\": [")
        append(newline)
        game.nodes.forEachIndexed { index, node ->
            append(indent).append(indent)
            append(nodeToJson(node))
            if (index < game.nodes.size - 1) append(",")
            append(newline)
        }
        append(indent)
        append("],")
        append(newline)

        // edges
        append(indent)
        append("\"edges\": [")
        append(newline)
        game.edges.forEachIndexed { index, edge ->
            append(indent).append(indent)
            append(edgeToJson(edge))
            if (index < game.edges.size - 1) append(",")
            append(newline)
        }
        append(indent)
        append("],")
        append(newline)

        // cpds
        append(indent)
        append("\"cpds\": [")
        append(newline)
        game.cpds.forEachIndexed { index, cpd ->
            append(indent).append(indent)
            append(cpdToJson(cpd, indent))
            if (index < game.cpds.size - 1) append(",")
            append(newline)
        }
        append(indent)
        append("],")
        append(newline)

        // tags
        append(indent)
        append("\"tags\": ")
        append(jsonStringList(game.tags))
        append(newline)

        append("}")
    }
}

private fun nodeToJson(node: MaidNode): String {
    return buildString {
        append("{")
        append("\"id\": ")
        append(jsonString(node.id))
        append(", \"type\": ")
        append(jsonString(node.type.jsonValue))
        if (node.agent != null) {
            append(", \"agent\": ")
            append(jsonString(node.agent))
        }
        append(", \"domain\": ")
        append(jsonAnyList(node.domain))
        append("}")
    }
}

private fun edgeToJson(edge: MaidEdge): String {
    return "{\"source\": ${jsonString(edge.source)}, \"target\": ${jsonString(edge.target)}}"
}

private fun cpdToJson(cpd: TabularCPD, indent: String): String {
    return buildString {
        append("{")
        append("\"node\": ")
        append(jsonString(cpd.node))
        append(", \"parents\": ")
        append(jsonStringList(cpd.parents))
        append(", \"values\": ")
        append(jsonDoubleMatrix(cpd.values))
        append("}")
    }
}

private fun jsonString(s: String): String {
    val escaped = s
        .replace("\\", "\\\\")
        .replace("\"", "\\\"")
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    return "\"$escaped\""
}

private fun jsonStringList(list: List<String>): String {
    return list.joinToString(", ", "[", "]") { jsonString(it) }
}

private fun jsonAnyList(list: List<Any>): String {
    return list.joinToString(", ", "[", "]") { jsonAny(it) }
}

private fun jsonAny(value: Any): String {
    return when (value) {
        is String -> jsonString(value)
        is Int -> value.toString()
        is Long -> value.toString()
        is Double -> {
            if (value.isNaN() || value.isInfinite()) "0.0"
            else if (value == value.toLong().toDouble()) value.toLong().toString()
            else value.toString()
        }
        is Float -> jsonAny(value.toDouble())
        is Boolean -> value.toString()
        is List<*> -> value.filterNotNull().joinToString(", ", "[", "]") { jsonAny(it) }
        else -> jsonString(value.toString())
    }
}

private fun jsonDoubleMatrix(matrix: List<List<Double>>): String {
    return matrix.joinToString(", ", "[", "]") { row ->
        row.joinToString(", ", "[", "]") { value ->
            if (value.isNaN() || value.isInfinite()) "0.0"
            else if (value == value.toLong().toDouble()) value.toLong().toString()
            else value.toString()
        }
    }
}

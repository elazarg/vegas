package vegas.backend.gambit

import vegas.Rational
import vegas.RoleId
import vegas.VarId


/**
 * Writes game trees in Gambit's EFG format with proper formatting.
 */
internal class EfgWriter(
    private val gameName: String,
    private val gameDescription: String,
    private val players: Set<RoleId>
) {
    private var outcomeCounter = 1
    private val infosetIdNormalized: MutableMap<RoleId, MutableMap<Int, Int>> = mutableMapOf()

    fun write(tree: GameTree): String {
        outcomeCounter = 1
        val header = buildHeader()
        val nodes = writeTree(tree)
        return "$header\n\n${nodes.joinToString("\n")}"
    }

    private fun buildHeader(): String {
        val playerList = players.joinToString(" ") { "\"${it.name}\"" }
        return """EFG 2 R "$gameName" { $playerList }
"$gameDescription""""
    }

    private fun writeTree(tree: GameTree): List<String> {
        return when (tree) {
            is GameTree.Decision -> writeDecision(tree)
            is GameTree.Terminal -> listOf(writeTerminal(tree))
        }
    }

    private fun writeDecision(node: GameTree.Decision): List<String> {
        val nodeType = if (node.isChance) "c" else "p"
        val nodeName = "\"\""
        val owner = if (node.isChance) "" else players.indexOf(node.owner) + 1
        val infosetMap = infosetIdNormalized.getOrPut(node.owner) { mutableMapOf() }
        val infosetNum = infosetMap.getOrPut(node.infosetId) { infosetMap.size + 1 }
        val infosetName = "\"\""

        val actions = node.choices.joinToString(" ") { choice ->
            val actionName = formatActionName(choice.action)
            val prob = if (node.isChance) formatRational(choice.probability ?: Rational(1)) else ""
            "\"$actionName\" $prob"
        }

        val line = "$nodeType $nodeName $owner $infosetNum $infosetName { $actions } 0".replace("  ", " ")

        val subtrees = node.choices.flatMap { writeTree(it.subtree) }
        return listOf(line) + subtrees
    }

    private fun writeTerminal(node: GameTree.Terminal): String {
        val nodeName = "\"\""
        val outcomeNum = outcomeCounter++
        val outcomeName = "\"\""
        val payoffs = players.joinToString(" ") { role ->
            formatValue(node.payoffs[role] ?: IrVal.IntVal(0))
        }
        return "t $nodeName $outcomeNum $outcomeName { $payoffs }"
    }

    private fun formatActionName(action: Map<VarId, IrVal>): String {
        if (action.isEmpty()) return "Quit"
        return action.values.joinToString("&") { formatValue(it) }
    }

    private fun formatValue(const: IrVal): String = when (const) {
        is IrVal.BoolVal -> const.v.toString()
        is IrVal.IntVal -> const.v.toString()
        is IrVal.Hidden -> "Hidden(${formatValue(const.inner)})"
        IrVal.Opaque -> "Opaque"
        IrVal.Quit -> "Quit"
    }

    private fun formatRational(r: Rational): String {
        return if (r.denominator == 1) {
            r.numerator.toString()
        } else {
            "${r.numerator}/${r.denominator}"
        }
    }
}

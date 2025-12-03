package vegas.backend.gambit

import vegas.Rational
import vegas.RoleId
import vegas.VarId
import vegas.ir.Expr.Const

private const val EFG_VERSION = "EFG 2 R"
private const val EMPTY_NAME = "\"\""
private const val QUIT_ACTION = "Quit"

/**
 * Writes game trees in Gambit's EFG format with proper formatting.
 */
internal class EfgWriter(
    private val gameName: String,
    private val gameDescription: String,
    players: Set<RoleId>
) {
    private val playerList = players.toList()
    private var outcomeCounter = 1
    private val infosetIdNormalized: MutableMap<RoleId, MutableMap<Int, Int>> = mutableMapOf()

    fun write(tree: GameTree): String {
        outcomeCounter = 1
        val header = buildHeader()
        val nodes = writeTree(tree)
        return "$header\n\n${nodes.joinToString("\n")}"
    }

    private fun buildHeader(): String {
        val playerNames = playerList.joinToString(" ") { "\"${it.name}\"" }
        return """$EFG_VERSION "$gameName" { $playerNames }
            |"$gameDescription"""".trimMargin()
    }

    private fun writeTree(tree: GameTree): List<String> {
        return when (tree) {
            is GameTree.Decision -> writeDecision(tree)
            is GameTree.Terminal -> listOf(writeTerminal(tree))
            is GameTree.Continuation -> {
                error(
                    "Cannot serialize game tree with unexpanded Continuation nodes. " +
                    "Call expand() to expand all branches before serializing to EFG format."
                )
            }
        }
    }

    private fun writeDecision(node: GameTree.Decision): List<String> {
        val nodeType = if (node.isChance) "c" else "p"
        val nodeName = EMPTY_NAME
        val owner = if (node.isChance) "" else playerList.indexOf(node.owner) + 1
        val infosetMap = infosetIdNormalized.getOrPut(node.owner) { mutableMapOf() }
        val infosetNum = infosetMap.getOrPut(node.infosetId) { infosetMap.size + 1 }
        val infosetName = EMPTY_NAME

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
        val nodeName = EMPTY_NAME
        val outcomeNum = outcomeCounter++
        val outcomeName = EMPTY_NAME
        val payoffs = playerList.joinToString(" ") { role ->
            formatValue(node.payoffs[role] ?: Const.IntVal(0))
        }
        return "t $nodeName $outcomeNum $outcomeName { $payoffs }"
    }

    private fun formatActionName(action: Map<VarId, Const>): String {
        if (action.isEmpty()) return QUIT_ACTION
        return action.values.joinToString("&") { formatValue(it) }
    }

    private fun formatValue(const: Const): String = when (const) {
        is Const.BoolVal -> const.v.toString()
        is Const.IntVal -> const.v.toString()
        is Const.Hidden -> "Hidden(${formatValue(const.inner)})"
        Const.Opaque -> "Opaque"
        Const.Quit -> QUIT_ACTION
    }

    private fun formatRational(r: Rational): String {
        return if (r.denominator == 1) {
            r.numerator.toString()
        } else {
            "${r.numerator}/${r.denominator}"
        }
    }
}

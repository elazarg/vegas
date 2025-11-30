package vegas.backend.gambit

import vegas.Rational
import vegas.RoleId
import vegas.VarId


/**
 * Main class for extensive form game generation.
 */
internal class ExtensiveFormGame(
    private val name: String,
    private val description: String,
    private val strategicPlayers: Set<RoleId>,
    private val tree: GameTree
) {
    fun toEfg(): String {
        val writer = EfgWriter(name, description, strategicPlayers)
        return writer.write(tree)
    }

    override fun toString(): String = toEfg()
}

/**
 * Represents an extensive form game tree.
 */
internal sealed class GameTree {
    /**
     * A decision/chance node in the game tree.
     * @property owner The role making the decision
     * @property infosetId Unique identifier for the information set
     * @property choices Available actions and their successor nodes
     * @property isChance Whether this is a chance node
     */
    data class Decision(
        val owner: RoleId,
        val infosetId: Int,
        val choices: List<Choice>,
        val isChance: Boolean = false
    ) : GameTree() {
        init {
            require(choices.isNotEmpty()) {
                "Decision node must have at least one choice"
            }
            if (isChance) {
                require(choices.all { it.probability != null }) {
                    "Chance nodes must have probabilities"
                }
                // Validate probabilities sum to 1
                val sum = choices.mapNotNull { it.probability }.fold(Rational(0, 1)) { acc, r -> acc + r }
                require(sum == Rational(1, 1)) {
                    "Chance node probabilities must sum to 1, got $sum"
                }
            }
        }
    }

    /**
     * A terminal node with payoffs.
     */
    data class Terminal(
        val payoffs: Map<RoleId, IrVal>
    ) : GameTree()

    /**
     * A single choice/action with its outcome.
     */
    data class Choice(
        val action: Map<VarId, IrVal>,
        val subtree: GameTree,
        val probability: Rational? = null  // Only for chance nodes
    )
}

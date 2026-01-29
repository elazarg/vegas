/**
 * # MAID Backend Data Structures
 *
 * Data classes representing Multi-Agent Influence Diagrams (MAIDs).
 * These match the JSON format expected by the Thrones game theory workbench.
 */
package vegas.backend.maid

/**
 * Node type in a MAID.
 */
enum class MaidNodeType(val jsonValue: String) {
    DECISION("decision"),
    UTILITY("utility"),
    CHANCE("chance");

    override fun toString(): String = jsonValue
}

/**
 * A node in a MAID (decision, utility, or chance).
 *
 * @property id Unique identifier for this node
 * @property type Node type (decision, utility, chance)
 * @property agent Owning agent (null for chance nodes)
 * @property domain Possible values for this node
 */
data class MaidNode(
    val id: String,
    val type: MaidNodeType,
    val agent: String?,
    val domain: List<Any>
)

/**
 * A directed edge in the MAID causal graph.
 *
 * @property source Source node ID
 * @property target Target node ID
 */
data class MaidEdge(
    val source: String,
    val target: String
)

/**
 * Tabular Conditional Probability Distribution.
 *
 * For utility nodes, this specifies the payoff as a function of parent values.
 * For chance nodes, this specifies the probability distribution.
 *
 * @property node Node this CPD belongs to
 * @property parents Parent node IDs in order (determines column indexing)
 * @property values Probability/payoff table. Each row corresponds to a domain value,
 *                  each column to a combination of parent values.
 */
data class TabularCPD(
    val node: String,
    val parents: List<String>,
    val values: List<List<Double>>
)

/**
 * A Multi-Agent Influence Diagram game.
 *
 * @property id Unique game identifier
 * @property title Human-readable game title
 * @property description Optional description
 * @property agents List of agent names (excluding chance roles)
 * @property nodes All nodes in the MAID
 * @property edges All directed edges in the causal graph
 * @property cpds Tabular CPD specifications
 * @property tags Metadata tags
 */
data class MaidGame(
    val id: String,
    val title: String,
    val description: String?,
    val agents: List<String>,
    val nodes: List<MaidNode>,
    val edges: List<MaidEdge>,
    val cpds: List<TabularCPD>,
    val tags: List<String> = listOf("vegas", "converted")
) {
    val formatName: String = "maid"
}

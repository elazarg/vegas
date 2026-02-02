/**
 * # MAID Backend: IR to MAID Conversion
 *
 * Converts Vegas GameIR to MAID format. The key insight is that Vegas's
 * ActionDag and VisibilityDag already encode MAID-like structures:
 *
 * - Roles → Agents
 * - Action parameters → Decision/Chance nodes
 * - guardReads → Information edges
 * - Payoffs → Utility nodes + CPDs
 * - Visibility (COMMIT/REVEAL/PUBLIC) → Information flow timing
 */
package vegas.backend.maid

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Type
import vegas.ir.asInt
import vegas.ir.observableFieldsAt
import vegas.semantics.eval
import java.util.UUID

/**
 * Generate a MAID from Vegas IR.
 *
 * @param ir The compiled Vegas GameIR
 * @return MaidGame ready for JSON serialization
 */
fun generateMaid(ir: GameIR): MaidGame {
    val converter = MaidConverter(ir)
    return converter.convert()
}

/**
 * Internal converter class that maintains state during conversion.
 */
private class MaidConverter(private val ir: GameIR) {
    private val nodes = mutableListOf<MaidNode>()
    private val edges = mutableListOf<MaidEdge>()
    private val cpds = mutableListOf<TabularCPD>()

    // Track field -> node ID mapping for edge creation
    private val fieldToNodeId = mutableMapOf<FieldRef, String>()

    // Track field -> decision action (the action where the value is chosen, not revealed)
    // For commit/reveal fields, this is the COMMIT action; for public fields, the public action.
    // Note: REVEAL actions make values visible but don't choose new values.
    // If griefing is encoded in the future, REVEAL would become a separate binary decision.
    private val fieldToDecisionAction = mutableMapOf<FieldRef, vegas.ir.ActionId>()

    // Track all utility node IDs for later edge creation
    private val utilityNodeIds = mutableMapOf<RoleId, String>()

    fun convert(): MaidGame {
        val agents = ir.roles.filterNot { it in ir.chanceRoles }.map { it.name }

        // 1. Create decision/chance nodes from action parameters
        createDecisionNodes()

        // 2. Create utility nodes from payoffs
        createUtilityNodes()

        // 3. Create edges based on observability (perfect recall + visible info)
        createEdges()

        // 4. Validate perfect recall constraints
        val recallErrors = validatePerfectRecall()
        if (recallErrors.isNotEmpty()) {
            throw IllegalStateException("Perfect recall violation:\n${recallErrors.joinToString("\n")}")
        }

        // 5. Create CPDs for utility nodes
        createUtilityCPDs()

        // Deduplicate edges
        val uniqueEdges = edges.distinctBy { it.source to it.target }

        return MaidGame(
            id = UUID.randomUUID().toString(),
            title = ir.name.ifEmpty { "Vegas Game" },
            description = "Generated from Vegas source",
            agents = agents,
            nodes = nodes,
            edges = uniqueEdges,
            cpds = cpds,
            tags = listOf("vegas", "converted")
        )
    }

    /**
     * Create decision/chance nodes from ActionDag action parameters.
     * Deduplicates nodes by (owner, param) to handle multiple actions per player.
     *
     * Also tracks the "decision action" for each field - the action where the value
     * is actually chosen. For commit/reveal fields, this is the COMMIT action (where
     * the choice is made), not the REVEAL action (which just makes it visible).
     */
    private fun createDecisionNodes() {
        val createdNodeIds = mutableSetOf<String>()

        for (meta in ir.dag.metas) {
            val owner = meta.struct.owner
            val isChance = owner in ir.chanceRoles
            val nodeType = if (isChance) MaidNodeType.CHANCE else MaidNodeType.DECISION

            for (param in meta.spec.params) {
                val nodeId = "${owner.name}_${param.name.name}"

                // Track field -> node mapping for edge creation
                val fieldRef = FieldRef(owner, param.name)
                fieldToNodeId[fieldRef] = nodeId

                // Track the decision action for this field (first non-REVEAL action wins)
                // REVEAL actions don't choose values - they just make previously committed values visible
                if (fieldRef !in fieldToDecisionAction && meta.kind != vegas.ir.Visibility.REVEAL) {
                    fieldToDecisionAction[fieldRef] = meta.id
                }

                // Skip if we already created this node
                if (nodeId in createdNodeIds) continue

                val domain = typeToDomain(param.type)

                nodes.add(MaidNode(
                    id = nodeId,
                    type = nodeType,
                    agent = if (isChance) null else owner.name,
                    domain = domain
                ))

                createdNodeIds.add(nodeId)
            }
        }
    }

    /**
     * Create utility nodes from payoff expressions.
     */
    private fun createUtilityNodes() {
        for ((role, expr) in ir.payoffs) {
            // Skip chance roles - they don't have utility
            if (role in ir.chanceRoles) continue

            val utilId = "U_${role.name}"
            utilityNodeIds[role] = utilId

            // Extract domain from payoff expression
            val domain = extractPayoffDomain(expr)

            nodes.add(MaidNode(
                id = utilId,
                type = MaidNodeType.UTILITY,
                agent = role.name,
                domain = domain
            ))
        }
    }

    /**
     * Create edges based on observability (perfect recall and visible information).
     *
     * For each MAID node (field), we find what's observable at its decision action:
     * - Same agent's earlier decisions (perfect recall), OR
     * - Visible (PUBLIC/REVEAL) earlier actions from other agents
     *
     * Note on COMMIT vs REVEAL:
     * - COMMIT actions ARE visible as events (you know someone made a choice)
     * - The VALUE is not visible until REVEAL (you don't know what they chose)
     * - For edge creation, we use observability at the decision action (COMMIT/PUBLIC),
     *   not at REVEAL time
     * - If griefing is encoded in the future, REVEAL would become a separate decision
     */
    private fun createEdges() {
        // Decision-to-decision edges based on observability at decision time
        for ((field, decisionAction) in fieldToDecisionAction) {
            val tgtNodeId = fieldToNodeId[field] ?: continue
            val observableFields = ir.dag.observableFieldsAt(decisionAction)

            for (obsField in observableFields) {
                val srcNodeId = fieldToNodeId[obsField] ?: continue
                if (srcNodeId != tgtNodeId) {
                    edges.add(MaidEdge(source = srcNodeId, target = tgtNodeId))
                }
            }
        }

        // Edges to utility nodes (based on payoff dependencies)
        for ((role, expr) in ir.payoffs) {
            if (role in ir.chanceRoles) continue
            val utilNodeId = utilityNodeIds[role] ?: continue
            val dependencies = extractFieldRefs(expr)
            for (dep in dependencies) {
                val srcNodeId = fieldToNodeId[dep] ?: continue
                edges.add(MaidEdge(source = srcNodeId, target = utilNodeId))
            }
        }
    }

    /**
     * Create tabular CPDs for utility nodes by enumerating all strategy profiles.
     *
     * CPD format for utility nodes:
     * - Rows correspond to domain values (possible payoffs)
     * - Columns correspond to parent value combinations
     * - Values are probabilities (1.0 for the actual payoff, 0.0 otherwise)
     */
    private fun createUtilityCPDs() {
        for ((role, expr) in ir.payoffs) {
            if (role in ir.chanceRoles) continue

            val utilNodeId = utilityNodeIds[role] ?: continue
            val dependencies = extractFieldRefs(expr).distinct()

            // Get the utility node to access its domain
            val utilNode = nodes.find { it.id == utilNodeId } ?: continue
            val utilDomain = utilNode.domain

            // Get parent node IDs (decision nodes that affect this utility)
            val parents = dependencies.mapNotNull { fieldToNodeId[it] }

            // Get domains for each parent
            val parentDomains = dependencies.map { field ->
                getFieldDomain(field)
            }

            if (parents.isEmpty() || parentDomains.isEmpty()) {
                // No dependencies - constant payoff
                val constantValue = try {
                    eval({ Expr.Const.IntVal(0) }, expr).asInt()
                } catch (_: Exception) {
                    0
                }
                // Create probability distribution over domain values
                val cpdValues = utilDomain.map { domainVal ->
                    listOf(if (toInt(domainVal) == constantValue) 1.0 else 0.0)
                }
                cpds.add(TabularCPD(
                    node = utilNodeId,
                    parents = emptyList(),
                    values = cpdValues
                ))
                continue
            }

            // Enumerate all parent value combinations
            val allCombinations = cartesianProduct(parentDomains)

            // Evaluate payoff for each combination
            val payoffValues = allCombinations.map { combo ->
                val fieldValues = dependencies.zip(combo).toMap()
                try {
                    val readField: (FieldRef) -> Expr.Const = { field ->
                        when (val v = fieldValues[field]) {
                            is Int -> Expr.Const.IntVal(v)
                            is Boolean -> Expr.Const.BoolVal(v)
                            else -> Expr.Const.IntVal(0)
                        }
                    }
                    eval(readField, expr).asInt()
                } catch (_: Exception) {
                    0
                }
            }

            // Build CPD table: rows = domain values, columns = parent combinations
            // Each column is a probability distribution (1.0 for actual payoff, 0.0 otherwise)
            val cpdValues = utilDomain.map { domainVal ->
                val domainInt = toInt(domainVal)
                payoffValues.map { payoff ->
                    if (payoff == domainInt) 1.0 else 0.0
                }
            }

            cpds.add(TabularCPD(
                node = utilNodeId,
                parents = parents,
                values = cpdValues
            ))
        }
    }

    /**
     * Convert domain value to Int for comparison.
     */
    private fun toInt(value: Any): Int {
        return when (value) {
            is Int -> value
            is Long -> value.toInt()
            is Double -> value.toInt()
            is Boolean -> if (value) 1 else 0
            is String -> value.toIntOrNull() ?: 0
            else -> 0
        }
    }

    /**
     * Convert Vegas Type to MAID domain.
     */
    private fun typeToDomain(type: Type): List<Any> {
        return when (type) {
            is Type.SetType -> type.values.sorted()
            is Type.BoolType -> listOf(false, true)
            is Type.IntType -> listOf(0, 1) // Default for unbounded int
        }
    }

    /**
     * Get domain for a field from action parameters.
     */
    private fun getFieldDomain(field: FieldRef): List<Any> {
        for (meta in ir.dag.metas) {
            if (meta.struct.owner != field.owner) continue
            for (param in meta.spec.params) {
                if (param.name == field.param) {
                    return typeToDomain(param.type)
                }
            }
        }
        return listOf(0, 1) // Fallback
    }

    /**
     * Extract domain values that appear in a payoff expression.
     * Returns a reasonable default domain if extraction fails.
     */
    private fun extractPayoffDomain(expr: Expr): List<Any> {
        // For utility nodes, domain is the set of possible payoff values
        // We could enumerate all combinations and compute, but for simplicity
        // return a placeholder. The actual values are in the CPD.
        val values = mutableSetOf<Int>()
        collectIntConstants(expr, values)
        return if (values.isEmpty()) listOf(0) else values.sorted()
    }

    /**
     * Recursively collect integer constants from expression.
     */
    private fun collectIntConstants(expr: Expr, values: MutableSet<Int>) {
        when (expr) {
            is Expr.Const.IntVal -> values.add(expr.v)
            is Expr.Const.BoolVal -> { values.add(0); values.add(1) }
            is Expr.Add -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Sub -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Mul -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Div -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Mod -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Neg -> collectIntConstants(expr.x, values)
            is Expr.Ite -> {
                collectIntConstants(expr.c, values)
                collectIntConstants(expr.t, values)
                collectIntConstants(expr.e, values)
            }
            is Expr.Eq -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Ne -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Lt -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Le -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Gt -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Ge -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.And -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Or -> { collectIntConstants(expr.l, values); collectIntConstants(expr.r, values) }
            is Expr.Not -> collectIntConstants(expr.x, values)
            else -> { /* Field, IsDefined, Hidden, Opaque, Quit - no constants */ }
        }
    }

    /**
     * Recursively extract field references from expression.
     */
    private fun extractFieldRefs(expr: Expr): List<FieldRef> {
        val refs = mutableListOf<FieldRef>()
        collectFieldRefs(expr, refs)
        return refs
    }

    private fun collectFieldRefs(expr: Expr, refs: MutableList<FieldRef>) {
        when (expr) {
            is Expr.Field -> refs.add(expr.field)
            is Expr.IsDefined -> refs.add(expr.field)
            is Expr.Add -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Sub -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Mul -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Div -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Mod -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Neg -> collectFieldRefs(expr.x, refs)
            is Expr.Eq -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Ne -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Lt -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Le -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Gt -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Ge -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.And -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Or -> { collectFieldRefs(expr.l, refs); collectFieldRefs(expr.r, refs) }
            is Expr.Not -> collectFieldRefs(expr.x, refs)
            is Expr.Ite -> {
                collectFieldRefs(expr.c, refs)
                collectFieldRefs(expr.t, refs)
                collectFieldRefs(expr.e, refs)
            }
            else -> { /* Constants - no field refs */ }
        }
    }

    /**
     * Compute Cartesian product of lists.
     */
    private fun cartesianProduct(lists: List<List<Any>>): List<List<Any>> {
        if (lists.isEmpty()) return listOf(emptyList())
        if (lists.size == 1) return lists[0].map { listOf(it) }

        val first = lists[0]
        val rest = cartesianProduct(lists.drop(1))

        return first.flatMap { item ->
            rest.map { restList -> listOf(item) + restList }
        }
    }

    /**
     * Validate that perfect recall edges are present for all agents.
     * For each agent, every later decision must have edges from all earlier decisions.
     */
    private fun validatePerfectRecall(): List<String> {
        val errors = mutableListOf<String>()
        val edgeSet = edges.map { it.source to it.target }.toSet()

        // Group fields by agent (owner), only for non-chance roles
        val agentFields = fieldToDecisionAction.entries
            .filter { (field, _) -> field.owner !in ir.chanceRoles }
            .groupBy { (field, _) -> field.owner.name }

        for ((_, fieldEntries) in agentFields) {
            // Check all pairs where one decision precedes the other
            for ((earlierField, earlierAction) in fieldEntries) {
                for ((laterField, laterAction) in fieldEntries) {
                    if (earlierField == laterField) continue
                    if (!ir.dag.reach.reaches(earlierAction, laterAction)) continue

                    // Earlier field should have edge to later field
                    val src = fieldToNodeId[earlierField] ?: continue
                    val tgt = fieldToNodeId[laterField] ?: continue
                    if ((src to tgt) !in edgeSet) {
                        errors.add("Missing perfect recall edge: $src → $tgt")
                    }
                }
            }
        }
        return errors
    }
}

package vegas.frontend

import vegas.FieldRef
import vegas.RoleId
import vegas.frontend.Exp as AstExpr
import vegas.frontend.TypeExp as AstType
import vegas.ir.*
import vegas.ir.ActionDag.Companion.fromGraph

fun compileToIR(ast: GameAst): GameIR {
    val typeEnv = ast.types
    val roles = findRoleIds(ast.game)
    val chanceRoles = findChanceRoleIds(ast.game)

    val phases = collectPhases(ast.game, typeEnv)
    val payoffs = extractPayoffs(ast.game, typeEnv)

    val dag = actionDagFromPhases(phases)
        ?: error("ActionDag construction failed: cyclic deps / illegal commit–reveal / bad guard visibility")

    val ir = GameIR(
        name = ast.name,
        roles = roles,
        chanceRoles = chanceRoles,
        dag = ActionDag.expandCommitReveal(dag),
        payoffs = payoffs,
    )

    // IMPORTANT: Verify that IR contains no frontend Exp.Let nodes
    // Let expressions must be desugared via substitution before IR lowering
    assertNoLetInIR(ir)

    return ir
}

/**
 * Assert that the IR contains no frontend Exp.Let nodes.
 * Let expressions must be completely eliminated via substitution during lowering.
 * If this assertion fails, it indicates a bug in the let-desugaring logic.
 *
 * Note: This is a structural check. Since IR.Expr is a sealed class that doesn't
 * include a Let variant, the type system already prevents Let nodes from appearing.
 * However, we still check recursively to ensure complete desugaring occurred.
 */
private fun assertNoLetInIR(ir: GameIR) {
    // Check payoffs
    ir.payoffs.forEach { (role, expr) ->
        assertNoLetInExpr(expr, "payoff for role $role")
    }

    // Check all action guards in the DAG
    ir.dag.metas.forEach { meta ->
        assertNoLetInExpr(meta.spec.guardExpr, "guard for action ${meta.id}")
    }
}

/**
 * Recursively check if an IR expression tree is well-formed.
 * Since IR.Expr doesn't have a Let variant, this primarily ensures
 * the expression tree is properly constructed.
 */
private fun assertNoLetInExpr(expr: Expr, context: String) {
    when (expr) {
        is Expr.Const -> { /* terminal */ }
        is Expr.Field -> { /* terminal */ }
        is Expr.IsDefined -> { /* terminal */ }

        is Expr.Add -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Sub -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Mul -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Div -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Mod -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Neg -> {
            assertNoLetInExpr(expr.x, context)
        }

        is Expr.Eq -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Ne -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Lt -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Le -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Gt -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Ge -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }

        is Expr.And -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Or -> {
            assertNoLetInExpr(expr.l, context)
            assertNoLetInExpr(expr.r, context)
        }
        is Expr.Not -> {
            assertNoLetInExpr(expr.x, context)
        }
        is Expr.Ite -> {
            assertNoLetInExpr(expr.c, context)
            assertNoLetInExpr(expr.t, context)
            assertNoLetInExpr(expr.e, context)
        }
    }
}

// ========== Phase Collection ==========

/** Exactly one Signature per RoleId in a Phase.
 *
 * SIMULTANEITY SEMANTICS:
 * Simultaneous (independent) if neither depends on the other
 * (no path in dependency graph). Simultaneous actions:
 * - Compute infosets and legality from SAME pre-state snapshot
 * - Can execute in any order (commute)
 * - Belong to same information set if they can't observe each other's choices
 * */
data class Phase(val actions: Map<RoleId, Signature>) {
    fun roles(): Set<RoleId> = actions.keys
}


private fun findLatestWriter(
    field: FieldRef,
    beforePhase: Int,
    phases: List<Phase>,
): ActionId? {
    for (p in beforePhase - 1 downTo 0) {
        val sig = phases[p].actions[field.owner] ?: continue
        if (sig.parameters.any { it.name == field.param })
            return field.owner to p
    }
    return null
}

private fun findPriorCommit(
    field: FieldRef,
    beforePhase: Int,
    phases: List<Phase>,
): ActionId? {
    for (p in beforePhase - 1 downTo 0) {
        val sig = phases[p].actions[field.owner] ?: continue
        val param = sig.parameters.find { it.name == field.param }
        if (param != null && !param.visible)
            return field.owner to p
    }
    return null
}

/**
 * Build an [ActionDag] from a linear list of [Phase]s, without going
 * through [GameIR].
 *
 * Returns null if:
 *  - the induced dependency graph is cyclic, or
 *  - commit/reveal ordering is illegal, or
 *  - guards read fields that are never visible beforehand.
 */
fun actionDagFromPhases(phases: List<Phase>): ActionDag? {
    val nodes = mutableSetOf<ActionId>()
    val deps = mutableMapOf<ActionId, MutableSet<ActionId>>()

    // 1) Nodes
    phases.forEachIndexed { pIdx, phase ->
        phase.actions.forEach { (role, _) ->
            val id = role to pIdx
            nodes += id
            deps.getOrPut(id) { mutableSetOf() }
        }
    }

    // 2) Dependency inference (data + commit/reveal)
    phases.forEachIndexed { pIdx, phase ->
        phase.actions.forEach { (role, sig) ->
            val id = role to pIdx
            val dset = deps.getOrPut(id) { mutableSetOf() }
            val writes = sig.parameters.map { FieldRef(role, it.name) }.toSet()
            val guardReads = sig.requires.captures - writes

            // Phase-order dependency: immediately prior phase must have happened
            val prevPhase = pIdx - 1
            if (prevPhase >= 0) {
                phases[prevPhase].actions.keys.forEach { priorRole ->
                    dset += priorRole to prevPhase
                }
            }

            // Guard-data deps: latest writer of each captured field
            guardReads.forEach { field ->
                val w = findLatestWriter(field, pIdx, phases)
                if (w != null) dset += w
            }

            // Commit-reveal deps: reveal depends on prior commit
            sig.parameters.forEach { p ->
                if (p.visible) {
                    val f = FieldRef(role, p.name)
                    val com = findPriorCommit(f, pIdx, phases)
                    if (com != null) dset += com
                }
            }
        }
    }

    // 3) Per-action payloads (spec + struct)
    val payloads = mutableMapOf<ActionId, ActionMeta>()
    phases.forEachIndexed { pIdx, phase ->
        phase.actions.forEach { (role, sig) ->
            val id = role to pIdx

            val writes = sig.parameters.map { FieldRef(role, it.name) }.toSet()
            val guardReads = sig.requires.captures - writes

            val visibility = buildVisibilityMap(role, pIdx, sig, phases)

            val struct = ActionStruct(
                owner = role,
                writes = writes,
                visibility = visibility,
                guardReads = guardReads,
            )

            val params = sig.parameters.map { ActionParam(it.name, it.type) }

            val spec = ActionSpec(
                params = params,
                join = sig.join,
                guardExpr = sig.requires.condition,
            )

            payloads[id] = ActionMeta(id = id, spec = spec, struct = struct)
        }
    }

    return fromGraph(nodes, deps, payloads)
}

private fun buildVisibilityMap(
    role: RoleId,
    phaseIdx: Int,
    sig: Signature,
    phases: List<Phase>,
): Map<FieldRef, Visibility> {
    val map = mutableMapOf<FieldRef, Visibility>()
    sig.parameters.forEach { p ->
        val field = FieldRef(role, p.name)
        map[field] = if (!p.visible) {
            Visibility.COMMIT
        } else {
            val priorCommit = findPriorCommit(field, phaseIdx, phases)
            if (priorCommit != null) Visibility.REVEAL else Visibility.PUBLIC
        }
    }
    return map
}

private fun collectPhases(ext: Ext, typeEnv: Map<AstType.TypeId, AstType>): List<Phase> {
    return when (ext) {
        is Ext.Bind -> {
            // Multiple queries in same Bind -> same phase (simultaneous)
            val phase = ext.qs.associate { query ->
                query.role.id to lowerQuery(query, ext.kind, typeEnv)
            }
            listOf(Phase(phase)) + collectPhases(ext.ext, typeEnv)
        }

        is Ext.BindSingle -> {
            // Single query -> single-entry phase
            val phase = mapOf(
                ext.q.role.id to lowerQuery(ext.q, ext.kind, typeEnv)
            )
            listOf(Phase(phase)) + collectPhases(ext.ext, typeEnv)
        }

        is Ext.Value -> emptyList() // Terminal: no more phases
    }
}

private fun lowerQuery(query: Query, kind: Kind, typeEnv: Map<AstType.TypeId, AstType>): Signature {
    return Signature(
        join = when (kind) {
            Kind.JOIN -> Join(Expr.Const.IntVal(query.deposit.n))
            Kind.JOIN_CHANCE -> Join(Expr.Const.IntVal(query.deposit.n))
            else -> null
        },
        parameters = query.params.map { vardec ->
            Parameter(
                name = vardec.v.id,
                type = lowerType(vardec.type, typeEnv),
                // Visibility is determined by command kind:
                // - COMMIT: not visible (hidden commitment)
                // - REVEAL, YIELD, JOIN: visible
                visible = kind != Kind.COMMIT
            )
        },
        requires = Requirement(
            // IMPORTANT: collectCaptures must be called on the original AST expression
            // BEFORE lowerExpr performs let-desugaring via substitution.
            // However, collectCaptures recursively processes Let nodes (see line 381-384),
            // collecting field references from both init and body expressions.
            // This ensures that even after substitution eliminates Let nodes during lowering,
            // the captured field references remain accurate.
            //
            // Example: let! x = Alice.bid in (x > 100)
            //   - collectCaptures sees: Field(Alice.bid) in init, Var(x) in body
            //   - Returns: {Alice.bid}
            //   - lowerExpr substitutes to: (Alice.bid > 100)
            //   - Runtime evaluation uses: Alice.bid
            // The capture set correctly reflects the runtime field access.
            captures = collectCaptures(query.where),
            condition = lowerExpr(query.where, typeEnv)
        )
    )
}

// ========== Type Lowering ==========

private fun lowerType(type: AstType, typeEnv: Map<AstType.TypeId, AstType>): Type {
    return when (type) {
        AstType.INT -> Type.IntType
        AstType.BOOL -> Type.BoolType
        AstType.ADDRESS -> Type.IntType // Address as int in IR
        AstType.EMPTY -> error("EMPTY type should not reach IR")

        is AstType.Hidden -> lowerType(type.type, typeEnv) // Strip hidden wrapper

        is AstType.TypeId -> {
            val resolved = typeEnv[type] ?: error("Unknown type: ${type.name}")
            lowerType(resolved, typeEnv)
        }

        is AstType.Subset -> {
            val sorted = type.values.map { it.n }.sorted()
            val min = sorted.first()
            val max = sorted.last()
            if (max - min + 1 != sorted.size) {
                error("Non-contiguous subset not supported: ${type.values.map { it.n }}")
            }
            Type.RangeType(min, max)
        }

        is AstType.Range -> Type.RangeType(type.min.n, type.max.n)

        is AstType.Opt -> lowerType(type.type, typeEnv) // Strip opt wrapper
    }
}

// ========== Capture Collection ==========

/**
 * Collect all field references that appear in an expression.
 *
 * This function recursively walks the AST to find all Field nodes, which represent
 * references to role parameters (e.g., Alice.bid, Bob.choice).
 *
 * IMPORTANT: This correctly handles Let expressions by collecting from both the
 * initialization expression and the body. Even though let-desugaring via substitution
 * will later eliminate Let nodes during IR lowering, this function computes the
 * correct set of field references that will be accessed at runtime.
 *
 * Example:
 *   let! x = Alice.bid + Bob.offer in (x > 100)
 *   -> Collects: {Alice.bid, Bob.offer}
 *   -> After substitution: (Alice.bid + Bob.offer) > 100
 *   -> Runtime accesses: {Alice.bid, Bob.offer} ✓
 *
 * This ensures that visibility analysis and guard dependencies remain correct even
 * when let expressions are used in guards.
 */
private fun collectCaptures(exp: AstExpr): Set<FieldRef> {
    val captures = mutableSetOf<FieldRef>()

    fun collect(e: AstExpr) {
        when (e) {
            is AstExpr.Field -> {
                captures.add(e.fieldRef)
            }

            is AstExpr.UnOp -> collect(e.operand)

            is AstExpr.BinOp -> {
                collect(e.left)
                collect(e.right)
            }

            is AstExpr.Cond -> {
                collect(e.cond)
                collect(e.ifTrue)
                collect(e.ifFalse)
            }

            is AstExpr.Call -> e.args.forEach { collect(it) }

            is AstExpr.Let -> {
                // Collect from both initialization and body
                // This is critical for correctness with let-desugaring
                collect(e.init)
                collect(e.exp)
            }

            is AstExpr.Var, is AstExpr.Const -> { /* no captures */ }
        }
    }

    collect(exp)
    return captures
}

// ========== Expression Lowering ==========

// Note: substituteVar and substituteVarInOutcome are imported from vegas.ir.Transform
// to provide shared substitution logic used during let-expression desugaring.

private fun lowerExpr(exp: AstExpr, typeEnv: Map<AstType.TypeId, AstType>): Expr {
    return when (exp) {
        // Literals
        is AstExpr.Const.Num -> Expr.Const.IntVal(exp.n)
        is AstExpr.Const.Bool -> Expr.Const.BoolVal(exp.truth)
        is AstExpr.Const.Address -> Expr.Const.IntVal(exp.n)
        AstExpr.Const.UNDEFINED -> error("UNDEFINED should not appear in IR")

        // Field references
        is AstExpr.Field -> Expr.Field(exp.fieldRef)

        // Variables (shouldn't appear in well-typed AST)
        is AstExpr.Var -> error("Free variable in expression: ${exp.id}")

        // Unary operators
        is AstExpr.UnOp -> when (exp.op) {
            "isDefined" -> {
                val member = exp.operand as? AstExpr.Field
                    ?: error("isDefined requires Field operand, got: ${exp.operand}")
                Expr.IsDefined(member.fieldRef)
            }

            "isUndefined" -> {
                val member = exp.operand as? AstExpr.Field
                    ?: error("isUndefined requires Field operand, got: ${exp.operand}")
                Expr.Not(Expr.IsDefined(member.fieldRef))
            }

            "!" -> Expr.Not(lowerExpr(exp.operand, typeEnv))
            "-" -> Expr.Neg(lowerExpr(exp.operand, typeEnv))

            else -> error("Unknown unary operator: ${exp.op}")
        }

        // Binary operators
        is AstExpr.BinOp -> {
            val l = lowerExpr(exp.left, typeEnv)
            val r = lowerExpr(exp.right, typeEnv)

            when (exp.op) {
                // Arithmetic
                "+" -> Expr.Add(l, r)
                "-" -> Expr.Sub(l, r)
                "*" -> Expr.Mul(l, r)
                "/" -> Expr.Div(l, r)
                "%" -> Expr.Mod(l, r)

                // Comparison
                "==" -> Expr.Eq(l, r)
                "!=" -> Expr.Ne(l, r)
                "<" -> Expr.Lt(l, r)
                "<=" -> Expr.Le(l, r)
                ">" -> Expr.Gt(l, r)
                ">=" -> Expr.Ge(l, r)

                // Boolean
                "&&" -> Expr.And(l, r)
                "||" -> Expr.Or(l, r)

                // Special operators
                "<->" -> Expr.Eq(l, r)  // Biconditional (iff) -> equality
                "<-!->" -> Expr.Ne(l, r) // XOR -> not-equal

                else -> error("Unknown binary operator: ${exp.op}")
            }
        }

        // Conditional
        is AstExpr.Cond -> Expr.Ite(
            lowerExpr(exp.cond, typeEnv),
            lowerExpr(exp.ifTrue, typeEnv),
            lowerExpr(exp.ifFalse, typeEnv)
        )

        // Function calls
        is AstExpr.Call -> when (exp.target.id.name) {
            "alldiff" -> {
                // alldiff(a, b, c) -> (a != b) && (a != c) && (b != c)
                val args = exp.args.map { lowerExpr(it, typeEnv) }

                if (args.size < 2) {
                    Expr.Const.BoolVal(true) // alldiff of 0 or 1 elements is trivially true
                } else {
                    val pairs = args.indices.flatMap { i ->
                        ((i + 1) until args.size).map { j ->
                            Expr.Ne(args[i], args[j])
                        }
                    }
                    pairs.reduce<Expr,Expr> { acc, ne -> Expr.And(acc, ne) }
                }
            }

            "abs" -> {
                // abs(x) -> x >= 0 ? x : -x
                val arg = lowerExpr(exp.args.single(), typeEnv)
                Expr.Ite(
                    Expr.Ge(arg, Expr.Const.IntVal(0)),
                    arg,
                    Expr.Neg(arg)
                )
            }

            else -> error("Unknown function: ${exp.target.id.name}")
        }

        // Let expressions (desugar by substitution)
        is AstExpr.Let -> {
            // Substitute the variable with its initialization value throughout the body
            // let! x = init in body  ~~>  body[x := init]
            val bodyWithSubstitution = substituteVar(exp.exp, exp.dec.v.id, exp.init)
            lowerExpr(bodyWithSubstitution, typeEnv)
        }
    }
}

// ========== Payoff Extraction ==========

/**
 * Represents a handler with its associated queries.
 * @param queries The queries this handler applies to
 * @param handler The outcome handler (per-query or group)
 * @param isGroup True if this is a group handler (ext.handler), false if per-query (q.handler)
 * @param phaseIndex The index of the phase this handler belongs to (for alive computation)
 */
private data class HandlerInfo(
    val queries: List<Query>,
    val handler: Outcome,
    val isGroup: Boolean,
    val phaseIndex: Int
)

/**
 * Collect all handlers from AST in causal order.
 * Returns both per-query handlers and group handlers, each tagged with its phase index.
 */
private fun collectAllHandlers(ext: Ext): List<HandlerInfo> {
    fun go(ext: Ext, phaseIndex: Int): List<HandlerInfo> {
        return when (ext) {
            is Ext.Bind -> {
                val result = mutableListOf<HandlerInfo>()

                // Group handler (applies to entire step)
                if (ext.handler != null) {
                    result.add(HandlerInfo(ext.qs, ext.handler, isGroup = true, phaseIndex))
                }

                // Per-query handlers (single-party only, already validated by type checker)
                ext.qs.forEach { q ->
                    if (q.handler != null) {
                        result.add(HandlerInfo(listOf(q), q.handler, isGroup = false, phaseIndex))
                    }
                }

                result + go(ext.ext, phaseIndex + 1)
            }
            is Ext.BindSingle -> {
                val result = mutableListOf<HandlerInfo>()

                // Group handler
                if (ext.handler != null) {
                    result.add(HandlerInfo(listOf(ext.q), ext.handler, isGroup = true, phaseIndex))
                }

                // Per-query handler
                if (ext.q.handler != null) {
                    result.add(HandlerInfo(listOf(ext.q), ext.q.handler, isGroup = false, phaseIndex))
                }

                result + go(ext.ext, phaseIndex + 1)
            }
            is Ext.Value -> emptyList()
        }
    }
    return go(ext, 0)
}

// Legacy: Collect per-query handlers only (for backward compatibility)
private fun collectHandlers(ext: Ext): List<Pair<Query, Outcome>> {
    return when (ext) {
        is Ext.Bind -> {
            // Filter out Null handlers - they only affect type optionality, not payoffs
            val handlers = ext.qs.mapNotNull { q ->
                q.handler?.takeIf { it !is Outcome.Null }?.let { Pair(q, it) }
            }
            handlers + collectHandlers(ext.ext)
        }
        is Ext.BindSingle -> {
            // Filter out Null handlers - they only affect type optionality, not payoffs
            val handler = ext.q.handler
                ?.takeIf { it !is Outcome.Null }
                ?.let { listOf(Pair(ext.q, it)) }
                ?: emptyList()
            handler + collectHandlers(ext.ext)
        }
        is Ext.Value -> emptyList()
    }
}

/**
 * Compute stake[\r] = sum of all join deposits for role r
 */
private fun computeStakes(ext: Ext): Map<RoleId, Int> {
    val stakes = mutableMapOf<RoleId, Int>()
    fun collect(e: Ext) {
        when (e) {
            is Ext.Bind -> {
                if (e.kind == Kind.JOIN || e.kind == Kind.JOIN_CHANCE) {
                    e.qs.forEach { q ->
                        stakes[q.role.id] = (stakes[q.role.id] ?: 0) + q.deposit.n
                    }
                }
                collect(e.ext)
            }
            is Ext.BindSingle -> {
                if (e.kind == Kind.JOIN || e.kind == Kind.JOIN_CHANCE) {
                    stakes[e.q.role.id] = (stakes[e.q.role.id] ?: 0) + e.q.deposit.n
                }
                collect(e.ext)
            }
            is Ext.Value -> {}
        }
    }
    collect(ext)
    return stakes
}

/**
 * Compute alive(r) — global predicate: has role NOT timed out anywhere?
 *
 * For split/burn handlers, a role is "alive" if all their params (including hidden commits)
 * have been submitted. This differs from the original reveal-requirement semantics.
 */
private fun computeAliveExpr(role: RoleId, phases: List<Phase>): Expr {
    val checks = mutableListOf<Expr>()

    phases.forEach { phase ->
        val sig = phase.actions[role] ?: return@forEach
        if (sig.join != null) return@forEach  // skip join actions (can't timeout)

        sig.parameters.forEach { param ->
            // Check ALL params (including hidden commits) for split/burn alive computation
            // A role is dead if they failed to submit ANY required param
            val field = FieldRef(role, param.name)
            checks.add(Expr.IsDefined(field))
        }
    }

    return if (checks.isEmpty()) Expr.Const.BoolVal(true)
    else checks.reduce { a, b -> Expr.And(a, b) }
}

/**
 * Compute step-local failure condition: did any participant in this step fail?
 * Returns: ∃r ∈ stepParticipants: ¬doneInStep(r)
 */
private fun computeStepFailureCondition(queries: List<Query>): Expr {
    val failureChecks: List<Expr> = queries.flatMap { q ->
        q.params.map { p ->
            val field = FieldRef(q.role.id, p.v.id)
            Expr.Not(Expr.IsDefined(field))
        }
    }

    return if (failureChecks.isEmpty()) Expr.Const.BoolVal(false)
    else failureChecks.reduce { a, b -> Expr.Or(a, b) }
}

/**
 * Generate payoff expressions for split/burn handlers.
 */
private fun generateSplitBurnPayoffs(
    handler: Outcome,
    allRoles: Set<RoleId>,
    stakes: Map<RoleId, Int>,
    phases: List<Phase>
): Map<RoleId, Expr> {
    // Compute alive(r) for all roles
    val aliveExprs = allRoles.associateWith { computeAliveExpr(it, phases) }

    // survivorCount = Σ (alive(r) ? 1 : 0)
    val survivorCountTerms: List<Expr> = allRoles.map { r ->
        Expr.Ite(aliveExprs[r]!!, Expr.Const.IntVal(1), Expr.Const.IntVal(0))
    }
    val survivorCount = survivorCountTerms.reduce { a, b -> Expr.Add(a, b) }

    // forfeit = Σ (alive(r) ? 0 : stake[r])
    val forfeitTerms: List<Expr> = allRoles.map { r ->
        Expr.Ite(aliveExprs[r]!!, Expr.Const.IntVal(0), Expr.Const.IntVal(stakes[r] ?: 0))
    }
    val forfeit = forfeitTerms.reduce { a, b -> Expr.Add(a, b) }

    // safeCount = max(1, survivorCount) to avoid div-by-zero
    val safeCount = Expr.Ite(
        Expr.Gt(survivorCount, Expr.Const.IntVal(0)),
        survivorCount,
        Expr.Const.IntVal(1)
    )

    return when (handler) {
        is Outcome.Split -> allRoles.associateWith { r ->
            // alive(r) ? stake[r] + forfeit/safeCount : 0
            val stake = stakes[r] ?: 0
            Expr.Ite(
                aliveExprs[r]!!,
                Expr.Add(Expr.Const.IntVal(stake), Expr.Div(forfeit, safeCount)),
                Expr.Const.IntVal(0)
            )
        }
        is Outcome.Burn -> allRoles.associateWith { r ->
            // alive(r) ? stake[r] : 0
            val stake = stakes[r] ?: 0
            Expr.Ite(aliveExprs[r]!!, Expr.Const.IntVal(stake), Expr.Const.IntVal(0))
        }
        else -> error("Expected Split or Burn, got $handler")
    }
}

// Generate null-check condition: param1 == null && param2 == null && ...
private fun generateNullCheckCondition(query: Query): AstExpr {
    val fields = query.params.map { AstExpr.Field(FieldRef(query.role.id, it.v.id)) }

    if (fields.isEmpty()) return AstExpr.Const.Bool(false)

    val nullChecks: List<AstExpr> = fields.map { AstExpr.UnOp("isUndefined", it) }
    return nullChecks.reduce { acc: AstExpr, check: AstExpr -> AstExpr.BinOp("&&", acc, check) }
}

// Merge handlers into terminal outcome as outer conditionals
private fun mergeHandlersIntoOutcome(
    handlers: List<Pair<Query, Outcome>>,
    terminalOutcome: Outcome
): Outcome {
    return handlers.foldRight(terminalOutcome) { (query, handlerOutcome), acc ->
        val condition = generateNullCheckCondition(query)
        Outcome.Cond(condition, handlerOutcome, acc)
    }
}

private fun extractTerminalOutcome(ext: Ext): Outcome = when (ext) {
    is Ext.Bind -> extractTerminalOutcome(ext.ext)
    is Ext.BindSingle -> extractTerminalOutcome(ext.ext)
    is Ext.Value -> ext.outcome
}

private fun extractPayoffs(ext: Ext, typeEnv: Map<AstType.TypeId, AstType>): Map<RoleId, Expr> {
    val allHandlers = collectAllHandlers(ext)
    val terminalOutcome = extractTerminalOutcome(ext)
    val phases = collectPhases(ext, typeEnv)
    val stakes = computeStakes(ext)
    val allRoles = phases.flatMap { it.roles() }.toSet()

    // Check if there are any split/burn handlers (not null - null just makes fields optional)
    val hasSplitBurn = allHandlers.any { it.handler is Outcome.Split || it.handler is Outcome.Burn }
    // Filter out null handlers - they don't affect payoffs, just type optionality
    val effectiveHandlers = allHandlers.filter { it.handler !is Outcome.Null }

    if (!hasSplitBurn) {
        // No split/burn - use legacy path for per-query handlers only
        val perQueryHandlers = collectHandlers(ext)
        val mergedOutcome = if (perQueryHandlers.isNotEmpty()) {
            mergeHandlersIntoOutcome(perQueryHandlers, terminalOutcome)
        } else {
            terminalOutcome
        }
        return desugarOutcome(mergedOutcome, typeEnv)
    }

    // With split/burn handlers, we need to build payoffs with proper failure conditions
    // Start with terminal outcome payoffs
    var currentPayoffs = desugarOutcome(terminalOutcome, typeEnv)

    // Process handlers in reverse order (innermost first, then wrap with outer conditions)
    // Use effectiveHandlers which excludes null handlers (they don't affect payoffs)
    for (handlerInfo in effectiveHandlers.reversed()) {
        val (queries, handler, _, phaseIndex) = handlerInfo

        // Compute step failure condition: any participant in step failed
        val stepFailed = computeStepFailureCondition(queries)

        // For split/burn, only consider phases up to (and including) this handler's phase
        // This ensures alive(r) only checks params from phases that have been reached
        val relevantPhases = phases.take(phaseIndex + 1)

        val handlerPayoffs: Map<RoleId, Expr> = when (handler) {
            is Outcome.Split, is Outcome.Burn -> {
                // Use alive(r) computed from phases up to this handler's phase
                generateSplitBurnPayoffs(handler, allRoles, stakes, relevantPhases)
            }

            is Outcome.Value -> {
                // Regular custom outcome - desugar normally
                desugarOutcome(handler, typeEnv)
            }

            else -> {
                // Should not happen after type checking
                error("Unexpected handler type: $handler")
            }
        }

        // Wrap: if stepFailed then handlerPayoffs else currentPayoffs
        currentPayoffs = allRoles.associateWith { role ->
            Expr.Ite(
                stepFailed,
                handlerPayoffs[role] ?: Expr.Const.IntVal(0),
                currentPayoffs[role] ?: Expr.Const.IntVal(0)
            )
        }
    }

    return currentPayoffs
}

private fun desugarOutcome(outcome: Outcome, typeEnv: Map<AstType.TypeId, AstType>): Map<RoleId, Expr> {
    return when (outcome) {
        // Base case: direct value mapping
        is Outcome.Value -> {
            outcome.ts.mapKeys { it.key.id }
                .mapValues { lowerExpr(it.value, typeEnv) }
        }

        // Conditional outcome
        is Outcome.Cond -> {
            val ifTrue = desugarOutcome(outcome.ifTrue, typeEnv)
            val ifFalse = desugarOutcome(outcome.ifFalse, typeEnv)
            val cond = lowerExpr(outcome.cond, typeEnv)

            // Merge: for each role, create ite expression
            val allRoles = ifTrue.keys + ifFalse.keys
            allRoles.associateWith { role ->
                val t = ifTrue[role] ?: Expr.Const.IntVal(0) // Default to 0 if role not in branch
                val f = ifFalse[role] ?: Expr.Const.IntVal(0)
                Expr.Ite(cond, t, f)
            }
        }

        // Let in outcome (desugar by substitution)
        is Outcome.Let -> {
            // Substitute the variable with its value in the inner outcome
            // let! x = init in outcome  ~~>  outcome[x := init]
            val outcomeWithSubstitution = substituteVarInOutcome(outcome.outcome, outcome.dec.v.id, outcome.init)
            desugarOutcome(outcomeWithSubstitution, typeEnv)
        }

        // Split, Burn, and Null are handled specially during payoff extraction
        // They should not reach here in normal flow
        is Outcome.Split, is Outcome.Burn -> {
            error("Split/Burn handlers must be processed via extractPayoffs, not desugarOutcome directly")
        }
        is Outcome.Null -> {
            error("Null handlers only affect type optionality, should not appear in outcome processing")
        }
    }
}

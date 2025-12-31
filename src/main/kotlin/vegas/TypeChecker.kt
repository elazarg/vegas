package vegas

import vegas.dag.Algo
import vegas.frontend.Ast
import vegas.frontend.Exp
import vegas.frontend.GameAst
import vegas.frontend.Ext
import vegas.frontend.Kind
import vegas.frontend.MacroDec
import vegas.frontend.Outcome
import vegas.frontend.Query
import vegas.frontend.TypeExp
import vegas.frontend.TypeExp.*
import vegas.frontend.SourceLoc
import vegas.frontend.Span
import vegas.frontend.compileToIR
import vegas.frontend.freeVars
import vegas.frontend.inlineMacros

/* -------------------------------------------------------------------------- */
/* Errors & Utilities                                                        */
/* -------------------------------------------------------------------------- */

internal class StaticError(reason: String, val node: Ast? = null) : RuntimeException(reason) {
    fun span(): Span? = node?.let { SourceLoc.get(it) }
}

private object Pretty {
    fun type(t: TypeExp): String = when (t) {
        INT -> "int"
        BOOL -> "bool"
        ADDRESS -> "address"
        EMPTY -> "Empty"
        is TypeId -> t.name
        is Hidden -> "hidden ${wrap(type(t.type))}"
        is Opt -> "opt ${wrap(type(t.type))}"
        is Subset -> "{${t.values.joinToString(",") { it.n.toString() }}}"
        is Range -> "{${t.min.n}..${t.max.n}}"
    }
    private fun wrap(s: String) = if (s.any { it == ' ' }) "($s)" else s
}

/**
 * Main Type Checker Entry Point.
 *
 * Architecture:
 * 1. **Universe Pass**: Validate type definitions and check for alias cycles.
 * 2. **Macro Pass**: Validate macro signatures and bodies in a pure context (no roles/fields).
 * 3. **Protocol Pass**: Typecheck the game mechanics (Join/Yield/Reveal/Commit) and flow.
 * 4. **IR/DAG Pass**: Compile to IR to validate causal structure (legacy).
 *
 * Key Invariants:
 * - **Commit Visibility**: Fields from `commit` are only visible to the owning role until `reveal`.
 *   From other players' POV: commit = declaration, reveal = definition, yield = both.
 * - **Deferred Where**: The `where` clause on `commit` is stored and checked at `reveal` time.
 * - **Optionality as Quit State**: The type `opt T` does not mean "nullable" in the general programming
 * sense. It specifically means "this value might be missing because the actor Quit".
 * - `YIELD`/`COMMIT` without a handler produces `opt T` (unsafe).
 * - `YIELD`/`COMMIT` with a handler produces `T` (safe).
 * - `JOIN` always produces `T` (cannot quit from join).
 */
fun typeCheck(program: GameAst) {
    // Pass A: Build Type Universe & Eagerly Validate
    val universe = TypeUniverse(program.types)
    universe.checkCycles()

    // Validate all top-level type definitions
    program.types.forEach { (_, typeExp) -> universe.validateDefined(typeExp, typeExp) }

    // Pass B: Macro Validation
    val macroChecker = MacroChecker(universe, program.macros)
    macroChecker.checkAll()

    // Pass C: Protocol Typing (The Core Pass)
    val protocolTyper = ProtocolTyper(universe, macroChecker.env)
    protocolTyper.typeGame(program.game)

    // Pass D: IR Structural Validation
    val inlined = inlineMacros(program)
    compileToIR(inlined)
}

/* ============================================================
 * A) Type universe / resolver
 * ============================================================ */

internal class TypeUniverse(
    private val aliases: Map<TypeId, TypeExp>
) {
    private val builtins: Map<String, TypeExp> = mapOf(
        "int" to INT,
        "bool" to BOOL,
        "address" to ADDRESS
    )

    // Memoized resolution
    private val memo = mutableMapOf<TypeId, TypeExp>()

    /** * Check for cycles in type aliases using graph analysis.
     * Uses Algo.findCycle to detect recursion like `type A = B; type B = A;`.
     */
    fun checkCycles() {
        val nodes = aliases.keys
        val edges = aliases.mapValues { (_, typeExp) ->
            extractTypeIds(typeExp).intersect(nodes)
        }

        val cycle = Algo.findCycle(nodes, edges)
        if (cycle.isNotEmpty()) {
            val firstId = aliases.keys.first { it.name == cycle.first().name }
            throw StaticError("Recursive type alias detected: ${cycle.joinToString(" -> ") { it.name }}", aliases[firstId])
        }
    }

    private fun extractTypeIds(t: TypeExp): Set<TypeId> {
        val ids = mutableSetOf<TypeId>()
        fun visit(x: TypeExp) {
            when (x) {
                is TypeId -> {
                    if (!builtins.containsKey(x.name)) ids.add(x)
                }
                is Hidden -> visit(x.type)
                is Opt -> visit(x.type)
                else -> {}
            }
        }
        visit(t)
        return ids
    }

    fun normalize(t: TypeExp): TypeExp = when (t) {
        is TypeId -> builtins[t.name] ?: t
        is Hidden -> Hidden(normalize(t.type))
        is Opt -> Opt(normalize(t.type))
        else -> t
    }

    fun resolve(t: TypeExp): TypeExp = when (val n = normalize(t)) {
        is TypeId -> resolveId(n)
        is Hidden -> Hidden(resolve(n.type))
        is Opt -> Opt(resolve(n.type))
        else -> n
    }

    private fun resolveId(id: TypeId): TypeExp {
        builtins[id.name]?.let { return it }
        memo[id]?.let { return it }

        val rhs = aliases[id] ?: return id // Unknown types handled by validateDefined

        val out = resolve(rhs)
        memo[id] = out
        return out
    }

    fun validateValueAnnotationType(t: TypeExp, node: Ast) {
        fun go(x: TypeExp) {
            when (resolve(x)) {
                is Hidden -> throw StaticError("'hidden' is internal-only; use 'commit' command instead", node)
                is Opt -> throw StaticError("'opt' is internal-only (quit optionality); not allowed in annotations", node)
                is TypeId -> {} // already validated by validateDefined
                else -> {}
            }
            // also recurse structurally to catch wrappers before resolve if you want
            when (x) {
                is Hidden -> go(x.type)
                is Opt -> go(x.type)
                else -> {}
            }
        }
        go(t)
    }

    fun validateDefined(t: TypeExp, node: Ast) {
        fun go(x: TypeExp) {
            when (val n = normalize(x)) {
                is TypeId -> {
                    if (builtins.containsKey(n.name)) return
                    if (!aliases.containsKey(n)) throw StaticError("Unknown type '${n.name}'", node)
                }
                is Hidden -> go(n.type)
                is Opt -> go(n.type)
                else -> {}
            }
        }
        go(t)
    }
}

/* ============================================================
 * B) Macro env + checking
 * ============================================================ */

internal class MacroChecker(
    private val universe: TypeUniverse,
    private val macros: List<MacroDec>
) {
    val env: Map<VarId, MacroDec> = macros.associateBy { it.name }.also {
        if (it.size != macros.size) throw StaticError("Duplicate macro definition", macros.first())
    }

    fun checkAll() {
        checkAcyclic()
        checkBodies()
    }

    private fun checkAcyclic() {
        val macroNames = env.keys
        val deps = macros.associate { macro ->
            val bound = macro.params.map { it.name }.toSet()
            macro.name to macro.body.freeVars(bound).intersect(macroNames).toMutableSet()
        }.toMutableMap()

        val cycle = Algo.findCycle(macros.map { it.name }.toSet(), deps)
        if (cycle.isNotEmpty()) {
            val first = macros.first { it.name == cycle.first() }
            throw StaticError("Recursive macro definitions detected: ${cycle.joinToString(" -> ")}", first)
        }
    }

    private fun checkBodies() {
        for (m in macros) {
            m.params.forEach {
                universe.validateDefined(it.type, it)
                validateNoHidden(it.type, it) // Macros cannot operate on Hidden types directly
            }
            universe.validateDefined(m.resultType, m)
            validateNoHidden(m.resultType, m)

            // Macros are typed in a pure environment
            val view = View(
                roles = emptySet(),
                fields = emptyMap(),
                vars = m.params.associate { it.name to it.type }
            )
            val tc = ExprTyper(universe, env)

            val bodyT = try {
                tc.type(m.body, view)
            } catch (e: StaticError) {
                throw StaticError("In macro '${m.name}': ${e.message}", m.body)
            }

            if (!tc.isSubtype(bodyT, m.resultType)) {
                throw StaticError(
                    "Macro '${m.name}' body type ${Pretty.type(bodyT)} does not match declared return type ${Pretty.type(m.resultType)}",
                    m.body
                )
            }
        }
    }

    private fun validateNoHidden(t: TypeExp, node: Ast) {
        val r = universe.resolve(t)
        if (containsHidden(r)) {
            throw StaticError("Macros cannot use 'hidden' types in parameters or return values. Access hidden data inside 'where' clauses instead.", node)
        }
    }

    private fun containsHidden(t: TypeExp): Boolean = when(t) {
        is Hidden -> true
        is Opt -> containsHidden(t.type)
        else -> false
    }
}

/* ============================================================
 * C) Expression typing with view + facts
 * ============================================================ */

/** * Path-sensitive facts accumulated during control flow analysis.
 * Used to narrow `opt T` to `T` when `isDefined(x)` is true.
 */
internal data class Facts(
    val nonNull: Set<FieldRef> = emptySet(),
    val isNull: Set<FieldRef> = emptySet()
) {
    fun negate() = Facts(nonNull = isNull, isNull = nonNull)
    fun merge(o: Facts) = Facts(nonNull = nonNull + o.nonNull, isNull = isNull + o.isNull)
    companion object { fun empty() = Facts() }
}

internal data class View(
    val roles: Set<RoleId>,
    val fields: Map<FieldRef, TypeExp>,
    val vars: Map<VarId, TypeExp>,
    val whereOwner: RoleId? = null,
    val facts: Facts = Facts.empty()
)

internal class ExprTyper(
    private val universe: TypeUniverse,
    private val macroEnv: Map<VarId, MacroDec>
) {
    fun type(e: Exp, view: View): TypeExp = when (e) {
        is Exp.Const.Num -> Subset(setOf(e))
        is Exp.Const.Bool -> BOOL
        is Exp.Const.Address -> ADDRESS

        is Exp.Var -> view.vars[e.id] ?: throw StaticError("Variable '${e.id.name}' is undefined", e)

        is Exp.Field -> fieldType(e.fieldRef, view, e)

        is Exp.UnOp -> typeUnOp(e, view)
        is Exp.BinOp -> typeBinOp(e, view)
        is Exp.Call -> typeCall(e, view)

        is Exp.Cond -> {
            val cT = type(e.cond, view)
            require(isSubtype(cT, BOOL)) { StaticError("Condition must be bool, found '${Pretty.type(cT)}'", e.cond) }

            val newFacts = extractFacts(e.cond)
            val factsTrue = view.facts.merge(newFacts)
            val factsFalse = view.facts.merge(newFacts.negate())

            val t1 = type(e.ifTrue, view.copy(facts = factsTrue))
            val t2 = type(e.ifFalse, view.copy(facts = factsFalse))

            val j = join(t1, t2)
            if (j == EMPTY) throw StaticError("Conditional branches are incompatible: ${Pretty.type(t1)} vs ${Pretty.type(t2)}", e)
            j
        }

        is Exp.Let -> {
            universe.validateDefined(e.dec.type, e)
            universe.validateValueAnnotationType(e.dec.type, e)
            val initT = type(e.init, view)
            if (!isSubtype(initT, e.dec.type)) {
                throw StaticError("Bad let initialization: expected ${Pretty.type(e.dec.type)}, got ${Pretty.type(initT)}", e.init)
            }
            type(e.exp, view.copy(vars = view.vars + (e.dec.v.id to e.dec.type)))
        }

        Exp.Const.UNDEFINED -> throw AssertionError("Internal: UNDEFINED expression")
    }

    fun isSubtype(actual: TypeExp, expected: TypeExp): Boolean {
        val a = universe.resolve(actual)
        val b = universe.resolve(expected)
        if (a == b) return true
        val j = join(a, b)
        return j == b
    }

    private fun require(condition: Boolean, error: () -> StaticError) {
        if (!condition) throw error()
    }

    /* ---------- Field access + contextual unhide ---------- */

    private fun fieldType(f: FieldRef, view: View, node: Ast): TypeExp {
        if (f.owner !in view.roles) throw StaticError("${f.owner} is not a role", node)
        val raw = view.fields[f] ?: throw StaticError("Field '$f' is undefined", node)

        // 1) Contextual unhide (ONLY in where(owner))
        val base = unhideIfOwner(raw, f, view)

        // 2) Apply facts narrowing (on Opt only)
        val resolved = universe.resolve(base)
        val narrowed = if (f in view.facts.nonNull && resolved is Opt) resolved.type else base

        return narrowed
    }

    private fun unhideIfOwner(raw: TypeExp, f: FieldRef, view: View): TypeExp {
        val owner = view.whereOwner ?: return raw
        if (f.owner != owner) return raw

        return when (val r = universe.resolve(raw)) {
            is Hidden -> universe.resolve(r.type) // hidden T -> T
            is Opt -> {
                val inner = universe.resolve(r.type)
                if (inner is Hidden) Opt(universe.resolve(inner.type)) else raw // opt hidden T -> opt T
            }
            else -> raw
        }
    }

    /* ---------- Operators ---------- */

    private fun typeUnOp(e: Exp.UnOp, view: View): TypeExp {
        return when (e.op) {
            "-" -> {
                val t = type(e.operand, view)
                require(isSubtype(t, INT)) { StaticError("Unary '-' expects int, got ${Pretty.type(t)}", e.operand) }
                INT
            }
            "!" -> {
                val t = type(e.operand, view)
                require(isSubtype(t, BOOL)) { StaticError("Unary '!' expects bool, got ${Pretty.type(t)}", e.operand) }
                BOOL
            }
            "isDefined", "isUndefined" -> {
                val fe = e.operand as? Exp.Field ?: throw StaticError("${e.op} requires a field reference", e)

                // Uses RAW (pre-narrow) type to check structural optionality
                val raw = view.fields[fe.fieldRef] ?: throw StaticError("Field '${fe.fieldRef}' is undefined", e)
                val r = universe.resolve(raw)

                if (r !is Opt) {
                    throw StaticError("Cannot check nullability of non-optional field '${fe.fieldRef}'. Optionality indicates a player could have quit.", e)
                }
                BOOL
            }
            else -> throw StaticError("Unknown unary operation '${e.op}'", e)
        }
    }

    private fun typeBinOp(e: Exp.BinOp, view: View): TypeExp {
        val l = type(e.left, view)
        val r = type(e.right, view)

        return when (e.op) {
            "+", "-", "*", "/", "%" -> {
                require(isSubtype(l, INT) && isSubtype(r, INT)) {
                    StaticError("Arithmetic operator '${e.op}' expects int,int; got ${Pretty.type(l)}, ${Pretty.type(r)}", e)
                }
                INT
            }
            ">", ">=", "<", "<=" -> {
                require(isSubtype(l, INT) && isSubtype(r, INT)) {
                    StaticError("Comparison operator '${e.op}' expects int,int; got ${Pretty.type(l)}, ${Pretty.type(r)}", e)
                }
                BOOL
            }
            "&&", "||" -> {
                require(isSubtype(l, BOOL) && isSubtype(r, BOOL)) {
                    StaticError("Logic operator '${e.op}' expects bool,bool", e)
                }
                BOOL
            }
            "==", "!=" -> {
                // Strict: both sides must have same optionality
                val lr = universe.resolve(l)
                val rr = universe.resolve(r)

                if ((lr is Opt) != (rr is Opt)) {
                    throw StaticError("Cannot compare optional and non-optional types: ${Pretty.type(l)} vs ${Pretty.type(r)}. Optional fields must be checked for presence first.", e)
                }

                // Strict: Forbid Hidden equality
                if (lr is Hidden || rr is Hidden) {
                    throw StaticError("Cannot compare hidden values (commitments) directly. Use explicit reveal or logic on opened values in 'where' clauses.", e)
                }

                // Compatibility check
                val lb = if (lr is Opt) lr.type else lr
                val rb = if (rr is Opt) rr.type else rr

                require(eqComparable(lb, rb)) {
                    StaticError("Incompatible types for equality: ${Pretty.type(l)} vs ${Pretty.type(r)}", e)
                }
                BOOL
            }
            "<->", "<-!->" -> {
                require(isSubtype(l, BOOL) && isSubtype(r, BOOL)) { StaticError("Iff/Xor operator expects bool,bool", e) }
                BOOL
            }
            else -> throw StaticError("Invalid binary operation '${e.op}'", e)
        }
    }

    private fun typeCall(e: Exp.Call, view: View): TypeExp {
        val args = e.args.map { type(it, view) }
        return when (e.target.id.name) {
            "abs" -> {
                require(args.size == 1 && isSubtype(args[0], INT)) { StaticError("abs(int) expects 1 argument", e) }
                INT
            }
            "alldiff" -> {
                require(args.all { isSubtype(it, INT) }) { StaticError("alldiff(int...) expects int arguments", e) }
                BOOL
            }
            else -> {
                val m = macroEnv[e.target.id] ?: throw StaticError("Unknown function or macro '${e.target.id.name}'", e)

                if (args.size != m.params.size) {
                    throw StaticError("Macro '${m.name}' expects ${m.params.size} arguments, got ${args.size}", e)
                }

                for ((i, arg) in args.withIndex()) {
                    val paramType = m.params[i].type
                    if (!isSubtype(arg, paramType)) {
                        throw StaticError(
                            "Argument ${i + 1} to '${m.name}' has type ${Pretty.type(arg)}, expected ${Pretty.type(paramType)}",
                            e.args[i]
                        )
                    }
                }
                universe.resolve(m.resultType)
            }
        }
    }

    private fun eqComparable(a: TypeExp, b: TypeExp): Boolean {
        val x = universe.resolve(a)
        val y = universe.resolve(b)
        // Hidden explicitly rejected in call site, so we just check primitives here
        return (isSubtype(x, INT) && isSubtype(y, INT)) ||
                (x == BOOL && y == BOOL) ||
                (x == ADDRESS && y == ADDRESS)
    }

    /* ---------- Facts extraction ---------- */

    fun extractFacts(e: Exp): Facts = when (e) {
        is Exp.UnOp -> when (e.op) {
            "isDefined" -> (e.operand as? Exp.Field)?.let { Facts(nonNull = setOf(it.fieldRef)) } ?: Facts.empty()
            "isUndefined" -> (e.operand as? Exp.Field)?.let { Facts(isNull = setOf(it.fieldRef)) } ?: Facts.empty()
            "!" -> extractFacts(e.operand).negate()
            else -> Facts.empty()
        }
        is Exp.BinOp -> when (e.op) {
            "&&" -> extractFacts(e.left).merge(extractFacts(e.right))
            else -> Facts.empty()
        }
        else -> Facts.empty()
    }

    /* ---------- Join Lattice ---------- */

    private fun join(t1: TypeExp, t2: TypeExp): TypeExp = when {
        t1 is Opt && t2 is Opt -> Opt(join(t1.type, t2.type))
        t1 is Opt -> Opt(join(t1.type, t2))
        t2 is Opt -> Opt(join(t1, t2.type))

        t1 is TypeId -> join(universe.resolve(t1), t2)
        t2 is TypeId -> join(t1, universe.resolve(t2))

        t1 == t2 -> t1

        t1 === INT && t2 is IntClass -> INT
        t2 === INT && t1 is IntClass -> INT

        t1 is Subset && t2 is Subset -> Subset(t1.values union t2.values)

        t1 is Range && t2 is Range -> Range(
            Exp.Const.Num(minOf(t1.min.n, t2.min.n)),
            Exp.Const.Num(maxOf(t1.max.n, t2.max.n))
        )

        t1 is Subset && t2 is Range -> join(t2, t1)
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { it.n }
            val min = minOf(t1.min.n, values.minOrNull()!!)
            val max = maxOf(t1.max.n, values.maxOrNull()!!)

            if (t2.values.size == (max - min + 1)) t2
            else Range(Exp.Const.Num(min), Exp.Const.Num(max))
        }

        else -> EMPTY
    }
}

/* ============================================================
 * D) Protocol checker (Ext)
 * ============================================================ */

internal class ProtocolTyper(
    private val universe: TypeUniverse,
    macroEnv: Map<VarId, MacroDec>
) {
    private val expr = ExprTyper(universe, macroEnv)

    data class State(
        val roles: Set<RoleId> = emptySet(),
        val fields: Map<FieldRef, TypeExp> = emptyMap()
    )

    fun typeGame(game: Ext) {
        typeExt(game, State())
    }

    private fun typeExt(ext: Ext, st: State) {
        when (ext) {
            is Ext.Value -> {
                // Pass View to Outcome to allow var scoping
                val view = View(roles = st.roles, fields = st.fields, vars = emptyMap())
                typeOutcome(ext.outcome, view)
            }
            is Ext.BindSingle -> typeExt(Ext.Bind(ext.kind, listOf(ext.q), ext.ext), st)
            is Ext.Bind -> {
                ext.qs.forEach { q -> q.params.forEach { (_, t) -> universe.validateDefined(t, q) } }

                if ((ext.kind == Kind.JOIN || ext.kind == Kind.JOIN_CHANCE) && ext.qs.any { it.handler != null }) {
                    throw StaticError("Quit handlers are not allowed on JOIN", ext)
                }
                if (ext.qs.size > 1 && ext.kind != Kind.JOIN && ext.kind != Kind.JOIN_CHANCE && ext.qs.any { it.handler != null }) {
                    throw StaticError("Quit handlers not supported on simultaneous actions", ext)
                }

                val deltaMaps = mutableListOf<Map<FieldRef, TypeExp>>()
                val roles2 = st.roles.toMutableSet()

                for (q in ext.qs) {
                    val role = q.role.id
                    val isJoin = ext.kind == Kind.JOIN || ext.kind == Kind.JOIN_CHANCE
                    val isReveal = ext.kind == Kind.REVEAL
                    val isCommit = ext.kind == Kind.COMMIT

                    if (isJoin) roles2 += role
                    else if (role !in roles2) throw StaticError("$role is not a role", q.role)

                    val m = q.params.associate { (k, tRaw) ->
                        val fr = FieldRef(role, k.id)
                        val t = when {
                            // Join fields are strictly present (non-nullable)
                            isJoin -> {
                                val base = stripOpt(universe.resolve(tRaw)) // join-time payload has a concrete type
                                if (ext.qs.size > 1) Opt(base) else base
                            }
                            // Reveal preserves previous structure (opt hidden T -> opt T)
                            isReveal -> revealTypeOf(fr, tRaw, st.fields, q)
                            // Commit wraps in Hidden (internally) - creates the commitment
                            isCommit -> {
                                val base = universe.resolve(tRaw)
                                // Commit with handler guarantees presence, otherwise Opt
                                if (q.handler != null) Hidden(base) else Opt(Hidden(base))
                            }
                            // Yield with handler guarantees presence (non-nullable)
                            q.handler != null -> stripOpt(universe.resolve(tRaw))
                            // Yield without handler is nullable (Opt T)
                            else -> Opt(universe.resolve(tRaw))
                        }
                        fr to t
                    }

                    checkWhere(q, st.copy(roles = roles2), m)

                    // Handler Policy B: Handlers can read all currently visible fields
                    // Note: handlers allowed on yield and commit (for quit behavior), not on join/reveal
                    if (!isJoin && !isReveal) checkHandler(q, roles2, st.fields)

                    deltaMaps += m
                }

                val newFields = st.fields + deltaMaps.flatMap { it.entries }.associate { it.key to it.value }
                typeExt(ext.ext, State(roles = roles2, fields = newFields))
            }
        }
    }

    private fun revealTypeOf(fr: FieldRef, declaredRevealType: TypeExp, fields: Map<FieldRef, TypeExp>, node: Ast): TypeExp {
        val prev = fields[fr] ?: throw StaticError("Reveal of unknown field $fr", node)
        val prevR = universe.resolve(prev)

        // Implicit Opt preservation: Reveal only opens the Hidden layer, it respects the Opt layer.
        val (wasOpt, inner) = when (prevR) {
            is Opt -> true to prevR.type
            else -> false to prevR
        }
        val innerR = universe.resolve(inner)
        if (innerR !is Hidden) throw StaticError("Parameter '$fr' must be hidden before reveal", node)

        val expected = universe.resolve(innerR.type)
        val got = universe.resolve(declaredRevealType)

        // Strict Payload Matching: declared type must match hidden content type
        if (!expr.isSubtype(got, expected) || !expr.isSubtype(expected, got)) {
            throw StaticError("Reveal type mismatch for '$fr': expected ${Pretty.type(expected)}, got ${Pretty.type(got)}", node)
        }

        return if (wasOpt) Opt(expected) else expected
    }

    private fun checkWhere(q: Query, st: State, localFields: Map<FieldRef, TypeExp>) {
        val locallyDefinedByActor =
            localFields.keys.filter { it.owner == q.role.id }.toSet()

        val view = View(
            roles = st.roles,
            fields = st.fields + localFields,
            vars = emptyMap(),
            whereOwner = q.role.id,
            facts = Facts(nonNull = locallyDefinedByActor)
        )

        val t = expr.type(q.where, view)
        if (!expr.isSubtype(t, BOOL)) throw StaticError("Where clause must be bool; got ${Pretty.type(t)}", q.where)

        for (f in referencedFields(q.where)) {
            val raw = (st.fields + localFields)[f] ?: throw StaticError("Field '$f' undefined", q.where)
            val core = deepStripOpt(universe.resolve(raw))
            if (core is Hidden && f.owner != q.role.id) {
                throw StaticError("Where clause uses $f before it is revealed", q.where)
            }
        }
    }

    private fun checkHandler(q: Query, roles: Set<RoleId>, visibleFields: Map<FieldRef, TypeExp>) {
        val h = q.handler ?: return
        if (h !is Outcome.Value) throw StaticError("Quit handler must be a simple withdraw outcome", h)

        val expected = roles - q.role.id
        val got = h.ts.keys.map { it.id }.toSet()
        if (got != expected) throw StaticError("Quit handler must allocate to exactly other roles (size ${expected.size})", h)

        for ((_, e) in h.ts) {
            // Handlers allow reading visible fields
            val view = View(roles = roles, fields = visibleFields, vars = emptyMap())
            val t = expr.type(e, view)
            if (!expr.isSubtype(t, INT)) throw StaticError("Handler payout must be int", e)
        }
    }

    private fun typeOutcome(o: Outcome, view: View) {
        when (o) {
            is Outcome.Value -> {
                for ((role, e) in o.ts) {
                    if (role.id !in view.roles) throw StaticError("${role.id} is not a role", role)
                    val t = expr.type(e, view)
                    if (!expr.isSubtype(t, INT)) throw StaticError("Outcome value must be int", e)
                }
            }
            is Outcome.Cond -> {
                val cT = expr.type(o.cond, view)
                if (!expr.isSubtype(cT, BOOL)) throw StaticError("Outcome condition must be bool", o.cond)

                val facts = expr.extractFacts(o.cond)
                val viewTrue  = view.copy(facts = view.facts.merge(facts))
                val viewFalse = view.copy(facts = view.facts.merge(facts.negate()))

                typeOutcome(o.ifTrue, viewTrue)
                typeOutcome(o.ifFalse, viewFalse)
            }
            is Outcome.Let -> {
                universe.validateDefined(o.dec.type, o)
                universe.validateValueAnnotationType(o.dec.type, o)
                val initT = expr.type(o.init, view)
                if (!expr.isSubtype(initT, o.dec.type)) throw StaticError("Bad outcome let init", o.init)

                // Scope variable for inner outcome
                val innerView = view.copy(vars = view.vars + (o.dec.v.id to o.dec.type))
                typeOutcome(o.outcome, innerView)
            }
        }
    }

    private fun stripOpt(t: TypeExp): TypeExp = if (t is Opt) t.type else t

    private fun deepStripOpt(t: TypeExp): TypeExp {
        var x = t
        while (x is Opt) x = x.type
        return x
    }

    private fun referencedFields(exp: Exp): Set<FieldRef> = when (exp) {
        is Exp.Field -> setOf(exp.fieldRef)
        is Exp.BinOp -> referencedFields(exp.left) + referencedFields(exp.right)
        is Exp.UnOp -> referencedFields(exp.operand)
        is Exp.Cond -> referencedFields(exp.cond) + referencedFields(exp.ifTrue) + referencedFields(exp.ifFalse)
        is Exp.Call -> exp.args.flatMap { referencedFields(it) }.toSet()
        is Exp.Let -> referencedFields(exp.init) + referencedFields(exp.exp)
        else -> emptySet()
    }
}

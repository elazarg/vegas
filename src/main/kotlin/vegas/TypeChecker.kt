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
import vegas.frontend.TypeExp.*
import vegas.frontend.SourceLoc
import vegas.frontend.Span
import vegas.frontend.TypeExp
import vegas.frontend.VarDec
import vegas.frontend.compileToIR
import vegas.frontend.freeVars
import vegas.frontend.inlineMacros

/* -------------------------------------------------------------------------- */
/*  Errors & pretty-print                                                     */
/* -------------------------------------------------------------------------- */

internal class StaticError(reason: String, val node: Ast? = null) : RuntimeException(reason) {
    fun span(): Span? = node?.let { SourceLoc.get(it) }
}

// Short helpers to keep call sites terse
private fun pt(t: TypeExp): String = Pretty.type(t)
private fun pvd(vd: VarDec): String = "${vd.v.id}: ${pt(vd.type)}"

/**
 * Normalize built-in type names to their singleton instances.
 * This ensures TypeId("int") is treated as INT, TypeId("bool") as BOOL, etc.
 */
private fun normalizeBuiltinType(t: TypeExp): TypeExp = when (t) {
    is TypeId -> when (t.name) {
        "int" -> INT
        "bool" -> BOOL
        "address" -> ADDRESS
        else -> t
    }
    is Hidden -> Hidden(normalizeBuiltinType(t.type))
    else -> t
}

private object Pretty {
    fun type(t: TypeExp): String = when (t) {
        INT -> "int"
        BOOL -> "bool"
        ADDRESS -> "address"
        EMPTY -> "∅"
        is TypeId -> t.name
        is Hidden -> "hidden ${wrapIfComplex(t.type)}"
        is Opt -> "opt ${wrapIfComplex(t.type)}"
        is Subset -> "{${t.values.joinToString(",") { it.n.toString() }}}"
        is Range -> "{${t.min.n}..${t.max.n}}"
    }

    private fun wrapIfComplex(t: TypeExp): String = when (t) {
        is TypeId, INT, BOOL, ADDRESS -> type(t)
        else -> "(${type(t)})"
    }

    fun exp(e: Exp): String = when (e) {
        is Exp.Const.Num -> e.n.toString()
        is Exp.Const.Bool -> e.truth.toString()
        is Exp.Const.Address -> "@${e.n}"
        is Exp.Const.Hidden -> "hidden(${exp(e.value)})"
        Exp.Const.UNDEFINED -> "undefined"
        is Exp.Var -> e.id.name
        is Exp.Field -> "${e.fieldRef.role}.${e.fieldRef.param}"
        is Exp.UnOp -> "${e.op}${paren(exp(e.operand))}"
        is Exp.BinOp -> "(${exp(e.left)} ${e.op} ${exp(e.right)})"
        is Exp.Cond -> "${paren(exp(e.cond))} ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)}"
        is Exp.Call -> "${e.target.id.name}(${e.args.joinToString(", ") { exp(it) }})"
        is Exp.Let -> "let! ${pvd(e.dec)} = ${exp(e.init)} in ${exp(e.exp)}"
    }

    private fun paren(s: String) = if (needsParen(s)) "($s)" else s
    private fun needsParen(s: String) = s.any { it == ' ' || it in charArrayOf('?', ':') }
}

fun requireStatic(b: Boolean, s: String, node: Ast) {
    if (!b) throw StaticError(s, node)
}

private fun buildTypeMap(program: GameAst): Map<TypeId, TypeExp> =
    program.types + mapOf(
        TypeId("bool") to BOOL,
        TypeId("int") to INT,
        TypeId("address") to ADDRESS
    )

fun typeCheck(program: GameAst) {
    // 1. Build macro environment and type map
    val macroEnv = buildMacroEnv(program.macros)
    val typeMap = buildTypeMap(program)

    // 2. Check macros: duplicates, cycles, bodies
    checkDuplicateMacros(program.macros)
    checkMacroAcyclicity(program.macros, macroEnv)
    val checker = Checker(typeMap, macroEnv = macroEnv)
    typecheckMacros(program.macros, macroEnv, typeMap)

    // 3. Run traditional type checking (game + where/withdraw)
    checker.type(program.game)

    // 4. Inline macros (desugar) - this must happen before IR compilation
    val inlined = inlineMacros(program)

    // 5. Validate ActionDag structure when possible
    try {
        compileToIR(inlined)  // Use inlined program, not original
    } catch (_: IllegalStateException) {
        // IR lowering not supported for this construct (e.g., let expressions)
        // Skip ActionDag validation - the game may type check but can't be compiled yet
    }
}

private class Checker(
    private val typeMap: Map<TypeId, TypeExp>,
    private val roles: Set<RoleId> = emptySet(),
    private val env: Env<TypeExp> = Env(),
    private val macroEnv: Map<VarId, MacroDec> = emptyMap()
) {

    private fun requireRole(role: RoleId, node: Ast) {
        requireStatic(role in roles, "$role is not a role", node)
    }

    private fun Env<TypeExp>.safeGetValue(f: FieldRef, node: Ast): TypeExp {
        requireRole(f.role, node)
        try {
            return getValue(f)
        } catch (_: NoSuchElementException) {
            throw StaticError("Field '$f' is undefined", node)
        }
    }

    /** Resolve builtins and type aliases, preserving Hidden. */
    fun resolve(t: TypeExp): TypeExp = when (val normalized = normalizeBuiltinType(t)) {
        is TypeId -> typeMap[normalized]?.let { resolve(it) } ?: normalized
        is Hidden -> Hidden(resolve(normalized.type))
        else -> normalized
    }

    fun stripHidden(t: TypeExp): TypeExp = when (t) {
        is Hidden -> stripHidden(t.type)
        else -> t
    }

    /* -------------------------- Protocol layer ---------------------------- */

    fun type(ext: Ext) {
        when (ext) {
            is Ext.Bind -> {
                ext.qs.forEach { q ->
                    for (c in q.params) {
                        val t = stripHidden(c.type)
                        if (t is TypeId && !typeMap.containsKey(t)) {
                            throw StaticError("Unknown type '${t.name}'", c.type)
                        }
                    }
                }
                val (newRoles, ms) = ext.qs.map { q ->
                    val m = q.params.associate { (k, type) -> FieldRef(q.role.id, k.id) to type }
                    when (ext.kind) {
                        Kind.JOIN, Kind.JOIN_CHANCE -> {
                            val newRole = setOf(q.role.id)
                            checkWhere(roles + newRole, m, q)
                            Pair(newRole, m)
                        }
                        Kind.YIELD -> {
                            requireRole(q.role.id, q.role)
                            checkWhere(roles, m, q)
                            Pair(emptySet(), m)
                        }
                        Kind.REVEAL -> {
                            requireRole(q.role.id, q.role)
                            m.forEach { (rf, revealedType) ->
                                val (role, field) = rf
                                val existing = env.safeGetValue(rf, q)
                                requireStatic(existing is Hidden, "Parameter '$role.$field' must be hidden", q)
                                val expected = (existing as Hidden).type
                                requireStatic(
                                    compatible(revealedType, expected) && compatible(expected, revealedType),
                                    "Reveal type mismatch for '${role.name}.${field.name}': expected ${pt(expected)}, got ${pt(revealedType)}",
                                    q
                                )
                            }
                            checkWhere(roles, m, q)
                            Pair(emptySet(), m)
                        }
                    }
                }.unzip()
                val checker = Checker(typeMap, roles + newRoles.union(), env withMap ms.union(), macroEnv)
                checker.type(ext.ext)
            }

            is Ext.BindSingle -> {
                type(Ext.Bind(ext.kind, listOf(ext.q), ext.ext))
            }

            is Ext.Value -> type(ext.outcome)
        }
    }

    // Extract all field references from an expression
    private fun getReferencedFields(exp: Exp): Set<FieldRef> = when (exp) {
        is Exp.Field -> setOf(exp.fieldRef)
        is Exp.BinOp -> getReferencedFields(exp.left) + getReferencedFields(exp.right)
        is Exp.UnOp -> getReferencedFields(exp.operand)
        is Exp.Cond -> getReferencedFields(exp.cond) +
                getReferencedFields(exp.ifTrue) +
                getReferencedFields(exp.ifFalse)
        is Exp.Call -> exp.args.flatMap { getReferencedFields(it) }.toSet()
        is Exp.Let -> getReferencedFields(exp.init) + getReferencedFields(exp.exp)
        is Exp.Var, is Exp.Const -> emptySet()
    }

    private fun checkWhere(n: Set<RoleId>, m: Map<FieldRef, TypeExp>, q: Query) {
        val newEnv = env withMap m
        requireStatic(
            Checker(typeMap, n, newEnv, macroEnv).type(q.where) == BOOL,
            "Where clause failed",
            q
        )

        // Validate: same-role hidden fields are ok (deferred checking)
        // Other-role hidden fields are NOT ok (use-before-def)
        getReferencedFields(q.where).forEach { fieldRef ->
            if (newEnv.safeGetValue(fieldRef, q) is Hidden && fieldRef.role != q.role.id) {
                throw StaticError("Where clause uses $fieldRef before it is revealed", q)
            }
        }
    }

    private fun type(outcome: Outcome) {
        when (outcome) {
            is Outcome.Cond -> {
                requireStatic(type(outcome.cond) == BOOL, "Outcome condition must be boolean", outcome)
                type(outcome.ifTrue)
                type(outcome.ifFalse)
            }

            is Outcome.Value -> {
                outcome.ts.forEach { (role, v) ->
                    requireRole(role.id, role)
                    requireStatic(type(v) == INT, "Outcome value must be an int", v)
                }
            }

            is Outcome.Let -> {
                requireStatic(type(outcome.init) == outcome.dec.type, "Bad initialization of let ext", outcome.init)
                Checker(typeMap, emptySet(), env + Pair(outcome.dec.v.id, outcome.dec.type), macroEnv)
                    .type(outcome.outcome)
            }
        }
    }

    fun typeExp(exp: Exp): TypeExp = type(exp)

    private fun type(exp: Exp): TypeExp = when (exp) {
        is Exp.Call -> {
            val argTypes = exp.args.map { type(it) }
            when (exp.target.id.name) {
                "abs" -> {
                    checkOp(INT, argTypes)
                    INT
                }
                "alldiff" -> {
                    // all args must be INT
                    checkOp(INT, argTypes)
                    BOOL
                }
                else -> {
                    // Check if it's a user macro
                    val macro = macroEnv[exp.target.id]
                    if (macro != null) {
                        checkMacroCall(macro, argTypes, exp, typeMap)
                        resolve(macro.resultType)
                    } else {
                        throw StaticError("Unknown function or macro '${exp.target.id.name}'", exp)
                    }
                }
            }
        }

        is Exp.UnOp -> {
            val operandType = type(exp.operand)
            when (exp.op) {
                "-" -> {
                    checkOp(INT, operandType); INT
                }
                "!" -> {
                    checkOp(BOOL, operandType); BOOL
                }
                "isUndefined", "isDefined" -> {
                    // Flow-sensitive checks would go here
                    BOOL
                }
                else -> throw StaticError("Invalid unary operation '${exp.op}'", exp)
            }
        }

        is Exp.BinOp -> {
            val left = type(exp.left)
            val right = type(exp.right)
            when (exp.op) {
                "+", "-", "*", "/" -> {
                    checkOp(INT, left, right); INT
                }

                ">", ">=", "<", "<=" -> {
                    checkOp(INT, left, right); BOOL
                }

                "||", "&&" -> {
                    checkOp(BOOL, left, right); BOOL
                }

                "==", "!=" -> {
                    requireStatic(
                        compatible(left, right) || compatible(right, left),
                        "${pt(left)} <> ${pt(right)} (1)",
                        exp
                    )
                    BOOL
                }

                "<->", "<-!->" -> {
                    requireStatic(
                        compatible(left, BOOL) && compatible(right, BOOL),
                        "Both sides of ${exp.op} must be bool; got ${pt(left)} and ${pt(right)}",
                        exp
                    )
                    BOOL
                }

                else -> throw StaticError("Invalid binary operation '${exp.op}'", exp)
            }
        }

        is Exp.Const.Num -> INT
        is Exp.Const.Address -> ADDRESS
        is Exp.Const.Bool -> BOOL
        is Exp.Const.Hidden -> Hidden(type(exp.value as Exp))

        is Exp.Var -> try {
            env.getValue(exp.id)
        } catch (_: NoSuchElementException) {
            throw StaticError("Variable '${exp}' is undefined", exp)
        }

        is Exp.Field -> env.safeGetValue(exp.fieldRef, exp)

        is Exp.Cond -> {
            checkOp(BOOL, type(exp.cond))
            join(type(exp.ifTrue), type(exp.ifFalse))
        }

        is Exp.Let -> {
            requireStatic(type(exp.init) == exp.dec.type, "Bad initialization of let exp", exp)
            Checker(typeMap, emptySet(), env + Pair(exp.dec.v.id, exp.dec.type), macroEnv).type(exp.exp)
        }

        Exp.Const.UNDEFINED -> throw AssertionError()
    }

    private fun checkOp(expected: TypeExp, args: Collection<TypeExp>) =
        checkOp(expected, *args.toTypedArray())

    private fun checkOp(expected: TypeExp, vararg args: TypeExp) {
        for (arg in args) {
            requireStatic(
                compatible(arg, expected),
                "Incompatible operator argument: Expected ${pt(expected)}, actual ${pt(arg)}",
                arg
            )
        }
    }

    /**
     * Compatibility: resolves aliases, strips Hidden, then:
     *  - equal types are compatible,
     *  - if join collapses to one side, types are compatible,
     *  - Range/Subset compatible if subset ⊆ range.
     */
    fun compatible(t1Raw: TypeExp, t2Raw: TypeExp): Boolean {
        val t1 = stripHidden(resolve(t1Raw))
        val t2 = stripHidden(resolve(t2Raw))

        // 1) Trivial equality
        if (t1 == t2) return true

        // 2) If their join collapses to one side, we consider them compatible
        val j = join(t1, t2)
        if (j == t1 || j == t2) return true

        // 3) Range <-> Subset: a subset is compatible with a range
        //    if *all* its elements lie inside the inclusive range.
        fun subsetWithinRange(sub: Subset, rng: Range): Boolean {
            val lo = rng.min.n
            val hi = rng.max.n
            return sub.values.all { v -> v.n in lo..hi }
        }

        return when {
            t1 is Range && t2 is Subset -> subsetWithinRange(t2, t1)
            t2 is Range && t1 is Subset -> subsetWithinRange(t1, t2)
            else -> false
        }
    }

    private fun join(t1: TypeExp, t2: TypeExp): TypeExp = when {
        t1 is Opt && t2 is Opt -> Opt(join(t1.type, t2.type))
        t1 is Opt -> Opt(join(t1.type, t2))
        t2 is Opt -> Opt(join(t1, t2.type))
        t1 == t2 -> t1

        t1 is TypeId -> {
            requireStatic(typeMap.containsKey(t1), "${pt(t1)} not in type map", t1)
            join(typeMap.getValue(t1), t2)
        }
        t2 is TypeId -> {
            requireStatic(typeMap.containsKey(t2), "${pt(t2)} not in type map", t2)
            join(t1, typeMap.getValue(t2))
        }

        t1 === TypeId("role") && t2 == TypeId("role") -> TypeId("role")
        t1 === ADDRESS && t2 === ADDRESS -> ADDRESS
        t1 === BOOL && t2 === BOOL -> BOOL
        t1 === INT && t2 is IntClass -> INT
        t1 === EMPTY || t2 === EMPTY -> EMPTY // TODO: is it not meet?
        t1 is IntClass && t2 === INT -> INT

        t1 is Subset && t2 is Subset -> Subset(t1.values union t2.values)

        t1 is Range && t2 is Range -> Range(
            Exp.Const.Num(minOf(t1.min.n, t2.min.n)),
            Exp.Const.Num(maxOf(t1.max.n, t2.max.n))
        )

        t1 is Subset && t2 is Range -> join(t2, t1) // symmetric with the next branch
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { it.n }
            val min = minOf(t1.min.n, values.minOrNull()!!)
            val max = maxOf(t1.max.n, values.maxOrNull()!!)
            if (t2.values.size == max - min) t2
            else Range(Exp.Const.Num(min), Exp.Const.Num(max))
        }

        else -> EMPTY
    }
}

/* -------------------------------------------------------------------------- */
/*  Macro validation (syntactic sugar only)                                   */
/* -------------------------------------------------------------------------- */

/**
 * Macros are first-order, pure expression functions that desugar before IR compilation.
 *
 * Validation pipeline:
 *
 * 1. Build macro environment ([buildMacroEnv])
 * 2. Check for duplicate names ([checkDuplicateMacros])
 * 3. Type check macro bodies ([typecheckMacros])
 * 4. Check acyclicity ([checkMacroAcyclicity])
 */

/** Build macro environment from macro declarations */
private fun buildMacroEnv(macros: List<MacroDec>): Map<VarId, MacroDec> =
    macros.associateBy { it.name }

/** Check for duplicate macro names */
private fun checkDuplicateMacros(macros: List<MacroDec>) {
    val seen = mutableSetOf<VarId>()
    for (macro in macros) {
        val name = macro.name
        if (name in seen) {
            throw StaticError("Duplicate macro definition: '$name'", macro)
        }
        seen.add(name)
    }
}

/** Type check all macro declarations */
private fun typecheckMacros(
    macros: List<MacroDec>,
    macroEnv: Map<VarId, MacroDec>,
    typeMap: Map<TypeId, TypeExp>
) {
    for (macro in macros) {
        typecheckMacro(macro, macroEnv, typeMap)
    }
}

/** Type check a single macro declaration */
private fun typecheckMacro(
    macro: MacroDec,
    macroEnv: Map<VarId, MacroDec>,
    typeMap: Map<TypeId, TypeExp>
) {
    // Build environment with macro parameters (no roles, no fields)
    val paramEnv = Env(
        g = macro.params.associate { param -> param.name to param.type },
        r = emptyMap(),
        h = emptyMap()
    )

    // Use Checker to type check body - macros can't access role fields
    val checker = Checker(typeMap, emptySet(), paramEnv, macroEnv)
    val bodyType = try {
        checker.typeExp(macro.body)
    } catch (e: StaticError) {
        throw StaticError("In macro '${macro.name}': ${e.message}", macro.body)
    }

    // Check that body type matches declared return type
    if (!checker.compatible(bodyType, macro.resultType)) {
        throw StaticError(
            "Macro '${macro.name}' body type ${pt(bodyType)} does not match declared return type ${pt(macro.resultType)}",
            macro
        )
    }
}

/** Type check macro calls - verify arity and argument types */
private fun checkMacroCall(
    macro: MacroDec,
    argTypes: List<TypeExp>,
    callSite: Exp.Call,
    typeMap: Map<TypeId, TypeExp>
) {
    // Check arity
    if (argTypes.size != macro.params.size) {
        throw StaticError(
            "Call to macro '${macro.name}' has ${argTypes.size} argument(s), but expected ${macro.params.size}",
            callSite
        )
    }

    // Reuse Checker.compatible algebra
    val checker = Checker(typeMap, emptySet(), Env(), emptyMap())

    // Check argument types
    for ((i, argType) in argTypes.withIndex()) {
        val paramType = macro.params[i].type
        if (!checker.compatible(argType, paramType)) {
            throw StaticError(
                "Argument ${i + 1} to macro '${macro.name}' has type ${pt(argType)}, but expected ${pt(paramType)}",
                callSite
            )
        }
    }
}

/** Check for cycles in macro call graph */
private fun checkMacroAcyclicity(
    macros: List<MacroDec>,
    macroEnv: Map<VarId, MacroDec>
) {
    val macroNames: Set<VarId> = macroEnv.keys

    // Build call graph: macro -> set of macros it calls
    val deps: MutableMap<VarId, MutableSet<VarId>> = mutableMapOf()
    for (macro in macros) {
        // Bound vars in a macro body: its parameters
        val bound = macro.params.map { it.name }.toSet()

        val calledMacros: Set<VarId> =
            macro.body.freeVars(bound).intersect(macroNames)

        deps[macro.name] = calledMacros.toMutableSet()
    }

    val nameSet = macros.map { it.name }.toSet()
    val cycle = Algo.findCycle(nameSet, deps)

    if (cycle.isNotEmpty()) {
        throw StaticError(
            "Recursive macro definitions detected: ${cycle.joinToString(" -> ")}",
            macros.first { it.name == cycle.first() }
        )
    }
}

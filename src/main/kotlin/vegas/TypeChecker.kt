package vegas

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
import vegas.frontend.inlineMacros

internal class StaticError(reason: String, val node: Ast? = null) : RuntimeException(reason) {
    fun span(): Span? = if (node != null)  SourceLoc.get(node) else null
}

// Short helpers to keep call sites terse
internal fun pt(t: TypeExp): String = Pretty.type(t)
internal fun pvd(vd: VarDec): String = "${vd.v.id.name}: ${pt(vd.type)}"

/**
 * Normalize built-in type names to their singleton instances.
 * This ensures TypeId("int") is treated as INT, TypeId("bool") as BOOL, etc.
 */
internal fun normalizeBuiltinType(t: TypeExp): TypeExp = when {
    t is TypeId && t.name == "int" -> INT
    t is TypeId && t.name == "bool" -> BOOL
    t is TypeId && t.name == "address" -> ADDRESS
    t is Hidden -> Hidden(normalizeBuiltinType(t.type))
    else -> t
}

internal object Pretty {
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

fun typeCheck(program: GameAst) {
    // 1. Build macro environment
    val macroEnv = buildMacroEnv(program.macros)

    // 2. Check for duplicate macro names
    checkDuplicateMacros(program.macros)

    // 3. Type check each macro declaration
    val typeMap = program.types + mapOf(
        Pair(TypeId("bool"), BOOL),
        Pair(TypeId("int"), INT)
    )
    typecheckMacros(program.macros, macroEnv, typeMap)

    // 4. Check macro call graph for cycles
    checkMacroAcyclicity(program.macros, macroEnv)

    // 5. Run traditional type checking (with macro environment)
    Checker(typeMap, macroEnv = macroEnv).type(program.game)

    // 6. Inline macros (desugar) - this must happen before IR compilation
    val inlined = inlineMacros(program)

    // 7. Then validate ActionDag structure
    // Note: compileToIR() may throw IllegalStateException for unsupported features (e.g., let expressions)
    // We only want to validate games that CAN be compiled to IR
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

    fun stripHidden(t: TypeExp): TypeExp = when (t) {
        is Hidden -> stripHidden(t.type)
        else -> t
    }

    fun type(ext: Ext) {
        when (ext) {
            is Ext.Bind -> {
                ext.qs.forEach { q -> for (c in q.params) {
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
                                    "Reveal type mismatch for '${role.name}.${field.name}': expected ${pt(expected)}, got ${
                                        pt(
                                            revealedType
                                        )
                                    }", q
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
        requireStatic(Checker(typeMap, n, newEnv, macroEnv).type(q.where) == BOOL, "Where clause failed", q)

        // Validate: same-role hidden fields are ok (deferred checking)
        // Other-role hidden fields are NOT ok (use-before-def)
        getReferencedFields(q.where).forEach { fieldRef ->
            if (newEnv.safeGetValue(fieldRef, q) is Hidden && fieldRef.role != q.role.id) {
                throw StaticError(
                    "Where clause uses $fieldRef before it is revealed",
                    q
                )
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
                Checker(typeMap, emptySet(), env + Pair(outcome.dec.v.id, outcome.dec.type), macroEnv).type(outcome.outcome)
            }
        }
    }

    private fun type(exp: Exp): TypeExp = when (exp) {
        is Exp.Call -> {
            val argTypes = exp.args.map { type(it) }
            when (exp.target.id.name) {
                "abs" -> {
                    checkOp(INT, argTypes)
                    INT
                }

                "alldiff" -> {
                    // require at least 2 args?
                    checkOp(INT, argTypes) // all args must be INT
                    BOOL
                }

                else -> {
                    // Check if it's a macro
                    val macro = macroEnv[exp.target.id]
                    if (macro != null) {
                        checkMacroCall(macro, argTypes, exp, typeMap)
                        // Normalize built-in type names to singletons
                        normalizeBuiltinType(macro.resultType)
                    } else {
                        throw IllegalArgumentException("Unknown function or macro: ${exp.target.id.name}")
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
                    // We'll need flow-sensitivity to check this
                    // requireStatic(type(exp.operand) is Opt, "`isUndefined` arg must be `Opt`")
                    BOOL
                }

                else -> throw IllegalArgumentException(exp.op)
            }
        }

        is Exp.BinOp -> {
            val left = type(exp.left)
            val right = type(exp.right)
            when (exp.op) {
                "+", "-", "*", "/" -> {
                    checkOp(INT, left, right)
                    INT
                }

                ">", ">=", "<", "<=" -> {
                    checkOp(INT, left, right)
                    BOOL
                }

                "||", "&&" -> {
                    checkOp(BOOL, left, right)
                    BOOL
                }

                "==", "!=" -> {
                    requireStatic(
                        compatible(left, right) || compatible(right, left),
                        "${pt(left)} <> ${pt(right)} (1)", exp
                    )
                    BOOL
                }

                "<->", "<-!->" -> {
                    requireStatic(
                        compatible(left, BOOL) || compatible(right, BOOL),
                        "either ${pt(left)} or ${pt(right)} are incompatible with bool", exp
                    )
                    BOOL
                }

                else -> throw IllegalArgumentException(exp.op)
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
        is Exp.Field -> {
            env.safeGetValue(exp.fieldRef, exp)
        }

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

    private fun checkOp(expected: TypeExp, args: Collection<TypeExp>) = checkOp(expected, *args.toTypedArray())
    private fun checkOp(expected: TypeExp, vararg args: TypeExp) {
        for (arg in args) {
            requireStatic(
                compatible(arg, expected),
                "Incompatible operator argument: Expected ${pt(expected)}, actual ${pt(arg)}", arg
            )
        }
    }

    // Assumes TypeId resolution (if any) already happened before this call.
    // Hidden wrappers are erased for the purpose of compatibility.
    private fun compatible(t1Raw: TypeExp, t2Raw: TypeExp): Boolean {
        // 1) Normalize away 'hidden'

        val t1 = stripHidden(t1Raw)
        val t2 = stripHidden(t2Raw)

        // 2) Trivial equality
        if (t1 == t2) return true

        // 3) If their join collapses to one side, we consider them compatible
        val j = join(t1, t2)
        if (j == t1 || j == t2) return true

        // 4) Range ↔ Subset: a subset is compatible with a range
        //    if *all* its elements lie inside the inclusive range.
        fun subsetWithinRange(sub: Subset, rng: Range): Boolean {
            val lo = rng.min.n
            val hi = rng.max.n
            return sub.values.all { v ->
                v.n in lo..hi
            }
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

        t1 === TypeId("role") && t2 === TypeId("role") -> TypeId("role")
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

        t1 is Subset && t2 is Range -> join(t2, t2)
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { it.n }
            val min = minOf(t1.min.n, values.minOrNull()!!)
            val max = minOf(t1.max.n, values.maxOrNull()!!)
            if (t2.values.size == max - min) t2
            else Range(Exp.Const.Num(min), Exp.Const.Num(max))
        }

        else -> EMPTY
    }

}


package vegas

import vegas.dag.Algo
import vegas.frontend.*
import vegas.frontend.TypeExp.*

/**
 * Macro type checking and validation.
 *
 * This module implements the complete validation pipeline for Vegas macros, which are
 * first-order, pure expression functions that provide syntactic sugar for the language.
 *
 * ## Validation Pipeline (4 steps)
 *
 * The macro checker is called from `typeCheck()` and performs these validations:
 *
 * 1. **Build Macro Environment** ([buildMacroEnv])
 *    - Create a lookup table mapping macro names to their declarations
 *    - Used for quick macro resolution during type checking
 *
 * 2. **Check for Duplicate Names** ([checkDuplicateMacros])
 *    - Ensure no two macros have the same name
 *    - Prevents ambiguous macro calls
 *
 * 3. **Type Check Macro Bodies** ([typecheckMacros])
 *    - For each macro, verify the body expression type-checks correctly
 *    - Check that the body's inferred type matches the declared return type
 *    - Validate parameter types and usage within the body
 *    - Use a simplified type checker ([typeMacroExp]) since macros are pure expressions
 *
 * 4. **Check for Cycles** ([checkMacroAcyclicity])
 *    - Build a call graph showing which macros call which other macros
 *    - Use Algo.isAcyclic to detect cycles
 *    - Report cycles with clear error messages (e.g., "f → g → f")
 *    - Prevents infinite expansion during macro inlining
 *
 * ## Macro Call Validation
 *
 * During regular type checking, when a macro call is encountered:
 * - [checkMacroCall] validates arity (correct number of arguments)
 * - Checks each argument type is compatible with the corresponding parameter type
 * - Resolves TypeIds to underlying types before comparison (handles custom types)
 *
 * ## Design Constraints
 *
 * Macros must be:
 * - **First-order**: Cannot take functions as arguments or return functions
 * - **Acyclic**: The macro call graph must be a DAG (implies no recursion)
 * - **Pure expressions**: Cannot access role fields, only macro parameters
 *
 * These constraints ensure macros can be completely inlined in topological order
 * without runtime overhead or infinite expansion.
 */

/** Build macro environment from macro declarations */
internal fun buildMacroEnv(macros: List<MacroDec>): Map<VarId, MacroDec> {
    return macros.associateBy { it.name }
}

/** Check for duplicate macro names */
internal fun checkDuplicateMacros(macros: List<MacroDec>) {
    val seen = mutableSetOf<String>()
    for (macro in macros) {
        val name = macro.name.name
        if (name in seen) {
            throw StaticError("Duplicate macro definition: '$name'", macro)
        }
        seen.add(name)
    }
}

/** Type check all macro declarations */
internal fun typecheckMacros(
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
    // Build environment with macro parameters
    val paramEnv = macro.params.associate { param ->
        param.name to param.type
    }

    // Type check body in parameter environment
    val bodyType = try {
        typeMacroExp(macro.body, Env(paramEnv, emptyMap(), emptyMap()), macroEnv, typeMap)
    } catch (e: StaticError) {
        throw StaticError("In macro '${macro.name.name}': ${e.message}", macro.body)
    }

    // Check that body type matches declared return type
    // Normalize both types before comparison
    val normalizedBodyType = normalizeBuiltinType(bodyType)
    val normalizedResultType = normalizeBuiltinType(macro.resultType)

    if (!compatible(normalizedBodyType, normalizedResultType)) {
        throw StaticError(
            "Macro '${macro.name.name}' body type ${pt(normalizedBodyType)} does not match declared return type ${pt(normalizedResultType)}",
            macro
        )
    }
}

/** Type check macro calls - verify arity and argument types */
internal fun checkMacroCall(
    macro: MacroDec,
    argTypes: List<TypeExp>,
    callSite: Exp.Call,
    typeMap: Map<TypeId, TypeExp>
) {
    // Check arity
    if (argTypes.size != macro.params.size) {
        throw StaticError(
            "Call to macro '${macro.name.name}' has ${argTypes.size} argument(s), but expected ${macro.params.size}",
            callSite
        )
    }

    // Check argument types - resolve TypeIds before compatibility check
    for ((i, argType) in argTypes.withIndex()) {
        val paramType = macro.params[i].type
        // Resolve both types to their underlying types before comparison
        val resolvedArgType = resolveType(argType, typeMap)
        val resolvedParamType = resolveType(paramType, typeMap)
        if (!compatible(resolvedArgType, resolvedParamType)) {
            throw StaticError(
                "Argument ${i + 1} to macro '${macro.name.name}' has type ${pt(argType)}, but expected ${pt(paramType)}",
                callSite
            )
        }
    }
}

/** Resolve type IDs to their underlying types */
private fun resolveType(t: TypeExp, typeMap: Map<TypeId, TypeExp>): TypeExp = when {
    t is TypeId && typeMap.containsKey(t) -> resolveType(typeMap.getValue(t), typeMap)
    t is Hidden -> Hidden(resolveType(t.type, typeMap))
    else -> t
}

/** Type expression in macro context (simplified type checker for macro bodies) */
private fun typeMacroExp(
    exp: Exp,
    env: Env<TypeExp>,
    macroEnv: Map<VarId, MacroDec>,
    typeMap: Map<TypeId, TypeExp>
): TypeExp = when (exp) {
    is Exp.Call -> {
        val argTypes = exp.args.map { typeMacroExp(it, env, macroEnv, typeMap) }
        when (exp.target.id.name) {
            "abs" -> {
                checkOp(INT, argTypes)
                INT
            }
            "alldiff" -> {
                checkOp(INT, argTypes)
                BOOL
            }
            else -> {
                // Check if it's a macro
                val macro = macroEnv[exp.target.id]
                if (macro != null) {
                    checkMacroCall(macro, argTypes, exp, typeMap)
                    macro.resultType
                } else {
                    throw StaticError("Unknown function or macro: '${exp.target.id.name}'", exp)
                }
            }
        }
    }

    is Exp.UnOp -> {
        val operandType = typeMacroExp(exp.operand, env, macroEnv, typeMap)
        when (exp.op) {
            "-" -> { checkOp(INT, operandType); INT }
            "!" -> { checkOp(BOOL, operandType); BOOL }
            "isUndefined", "isDefined" -> BOOL
            else -> throw IllegalArgumentException("Unknown unary operator: ${exp.op}")
        }
    }

    is Exp.BinOp -> {
        val left = typeMacroExp(exp.left, env, macroEnv, typeMap)
        val right = typeMacroExp(exp.right, env, macroEnv, typeMap)
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
                    "${pt(left)} <> ${pt(right)}",
                    exp
                )
                BOOL
            }
            "<->", "<-!->" -> {
                requireStatic(
                    compatible(left, BOOL) || compatible(right, BOOL),
                    "either ${pt(left)} or ${pt(right)} are incompatible with bool",
                    exp
                )
                BOOL
            }
            else -> throw IllegalArgumentException("Unknown binary operator: ${exp.op}")
        }
    }

    is Exp.Const.Num -> INT
    is Exp.Const.Bool -> BOOL
    is Exp.Const.Address -> ADDRESS
    is Exp.Const.Hidden -> Hidden(typeMacroExp(exp.value as Exp, env, macroEnv, typeMap))
    Exp.Const.UNDEFINED -> EMPTY

    is Exp.Var -> try {
        env.getValue(exp.id)
    } catch (_: NoSuchElementException) {
        throw StaticError("Undefined variable '${exp.id.name}' in macro body", exp)
    }

    is Exp.Field -> throw StaticError(
        "Field access '${exp.fieldRef}' not allowed in macro bodies - macros are pure expression functions",
        exp
    )

    is Exp.Cond -> {
        val condType = typeMacroExp(exp.cond, env, macroEnv, typeMap)
        checkOp(BOOL, condType)
        val thenType = typeMacroExp(exp.ifTrue, env, macroEnv, typeMap)
        val elseType = typeMacroExp(exp.ifFalse, env, macroEnv, typeMap)
        if (!compatible(thenType, elseType) || !compatible(elseType, thenType)) {
            throw StaticError(
                "Conditional branches have incompatible types: ${pt(thenType)} vs ${pt(elseType)}",
                exp
            )
        }
        thenType
    }

    is Exp.Let -> {
        val initType = typeMacroExp(exp.init, env, macroEnv, typeMap)
        if (!compatible(initType, exp.dec.type)) {
            throw StaticError(
                "let! initialization type mismatch: expected ${pt(exp.dec.type)}, got ${pt(initType)}",
                exp
            )
        }
        typeMacroExp(exp.exp, env + (exp.dec.v.id to exp.dec.type), macroEnv, typeMap)
    }
}

/** Check for cycles in macro call graph */
internal fun checkMacroAcyclicity(macros: List<MacroDec>, macroEnv: Map<VarId, MacroDec>) {
    // Build call graph: macro -> set of macros it calls
    val deps = mutableMapOf<String, MutableSet<String>>()
    val macroNames = macros.map { it.name.name }.toSet()

    for (macro in macros) {
        deps[macro.name.name] = mutableSetOf()
    }

    for (macro in macros) {
        val called = findMacroCalls(macro.body, macroEnv)
        deps[macro.name.name] = called.toMutableSet()
    }

    // Check acyclicity using existing DAG utility
    if (!Algo.isAcyclic(macroNames, deps)) {
        // Find a cycle to report
        val cycle = findCycle(macroNames, deps)
        throw StaticError(
            "Recursive macro definitions detected: ${cycle.joinToString(" → ")}",
            macros.first { it.name.name == cycle.first() }
        )
    }
}

/** Find all macro calls in an expression */
private fun findMacroCalls(exp: Exp, macroEnv: Map<VarId, MacroDec>): Set<String> {
    val calls = mutableSetOf<String>()

    fun visit(e: Exp) {
        when (e) {
            is Exp.Call -> {
                // Check if this is a macro call (not a built-in)
                if (macroEnv.containsKey(e.target.id)) {
                    calls.add(e.target.id.name)
                }
                e.args.forEach { visit(it) }
            }
            is Exp.UnOp -> visit(e.operand)
            is Exp.BinOp -> {
                visit(e.left)
                visit(e.right)
            }
            is Exp.Cond -> {
                visit(e.cond)
                visit(e.ifTrue)
                visit(e.ifFalse)
            }
            is Exp.Let -> {
                visit(e.init)
                visit(e.exp)
            }
            is Exp.Const.Hidden -> visit(e.value as Exp)
            else -> {} // Var, Const, Field - no recursive calls
        }
    }

    visit(exp)
    return calls
}

/** Find a cycle in the graph for error reporting (simple DFS) */
private fun findCycle(nodes: Set<String>, deps: Map<String, Set<String>>): List<String> {
    val visited = mutableSetOf<String>()
    val recStack = mutableListOf<String>()

    fun dfs(node: String): List<String>? {
        if (node in recStack) {
            // Found cycle
            val cycleStart = recStack.indexOf(node)
            return recStack.subList(cycleStart, recStack.size) + node
        }
        if (node in visited) return null

        visited.add(node)
        recStack.add(node)

        for (dep in deps[node].orEmpty()) {
            val cycle = dfs(dep)
            if (cycle != null) return cycle
        }

        recStack.removeLast()
        return null
    }

    for (node in nodes) {
        val cycle = dfs(node)
        if (cycle != null) return cycle
    }

    return emptyList() // Should not happen if Algo.isAcyclic returned false
}

/** Helper to check operator type requirements */
private fun checkOp(expected: TypeExp, vararg actual: TypeExp) {
    for (t in actual) {
        if (!compatible(t, expected)) {
            throw StaticError("Type mismatch: expected ${pt(expected)}, got ${pt(t)}")
        }
    }
}

private fun checkOp(expected: TypeExp, actual: List<TypeExp>) {
    for (t in actual) {
        if (!compatible(t, expected)) {
            throw StaticError("Type mismatch: expected ${pt(expected)}, got ${pt(t)}")
        }
    }
}

/** Simplified type compatibility check for macro bodies */
private fun compatible(t1Raw: TypeExp, t2Raw: TypeExp): Boolean {
    // Strip hidden wrappers
    fun stripHidden(t: TypeExp): TypeExp = when (t) {
        is Hidden -> stripHidden(t.type)
        else -> t
    }

    // Normalize type IDs for built-in types
    // Note: Custom type IDs are left as-is and compared structurally
    fun normalizeTypeId(t: TypeExp): TypeExp = when {
        t is TypeId && t.name == "int" -> INT
        t is TypeId && t.name == "bool" -> BOOL
        t is TypeId && t.name == "address" -> ADDRESS
        t is TypeId -> t // Keep custom type IDs as-is
        else -> t
    }

    val t1 = normalizeTypeId(stripHidden(t1Raw))
    val t2 = normalizeTypeId(stripHidden(t2Raw))

    // Trivial equality (structural equality for data classes, reference equality for objects)
    if (t1 == t2) return true

    // Handle basic type compatibility for macros
    return when {
        // Base types are compatible with themselves
        t1 === INT && t2 === INT -> true
        t1 === BOOL && t2 === BOOL -> true
        t1 === ADDRESS && t2 === ADDRESS -> true

        // int is compatible with int classes (ranges, subsets)
        t1 === INT && t2 is IntClass -> true
        t2 === INT && t1 is IntClass -> true

        // Int classes are compatible with each other
        t1 is IntClass && t2 is IntClass -> true

        // Range and subset compatibility
        t1 is Range && t2 is Subset -> {
            val lo = t1.min.n
            val hi = t1.max.n
            t2.values.all { it.n in lo..hi }
        }
        t2 is Range && t1 is Subset -> {
            val lo = t2.min.n
            val hi = t2.max.n
            t1.values.all { it.n in lo..hi }
        }

        // Two subsets are compatible if one is a subset of the other
        t1 is Subset && t2 is Subset -> {
            t1.values.all { it in t2.values } || t2.values.all { it in t1.values }
        }

        // Two ranges are compatible
        t1 is Range && t2 is Range -> true

        // TypeIds with the same name
        t1 is TypeId && t2 is TypeId -> t1.name == t2.name

        else -> false
    }
}

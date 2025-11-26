package vegas

import vegas.dag.Algo
import vegas.frontend.*
import vegas.frontend.TypeExp.*

/**
 * Macro validation for Vegas.
 *
 * Macros are first-order, pure expression functions that desugar before IR compilation.
 *
 * ## Validation Pipeline
 *
 * 1. **Build Macro Environment** ([buildMacroEnv])
 * 2. **Check for Duplicate Names** ([checkDuplicateMacros])
 * 3. **Type Check Macro Bodies** ([typecheckMacros])
 *    - Reuses [Checker] with parameter-only environment (no roles/fields)
 * 4. **Check Acyclicity** ([checkMacroAcyclicity])
 *    - Ensures macro call graph is a DAG (prevents infinite expansion)
 *
 * ## Design Constraints
 *
 * - **First-order**: No function parameters or returns
 * - **Acyclic**: Call graph must be a DAG
 * - **Pure**: Can only access parameters, not role fields
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
        throw StaticError("In macro '${macro.name.name}': ${e.message}", macro.body)
    }

    // Check that body type matches declared return type
    // Normalize both types before comparison
    val normalizedBodyType = normalizeBuiltinType(bodyType)
    val normalizedResultType = normalizeBuiltinType(macro.resultType)

    if (!checker.compatible(normalizedBodyType, normalizedResultType)) {
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

    // Create a checker to use its compatible method
    val checker = Checker(typeMap, emptySet(), Env(), emptyMap())

    // Check argument types - resolve TypeIds before compatibility check
    for ((i, argType) in argTypes.withIndex()) {
        val paramType = macro.params[i].type
        // Resolve both types to their underlying types before comparison
        val resolvedArgType = resolveType(argType, typeMap)
        val resolvedParamType = resolveType(paramType, typeMap)
        if (!checker.compatible(resolvedArgType, resolvedParamType)) {
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

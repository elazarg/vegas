package vegas.frontend

import vegas.VarId

/**
 * Macro inlining / desugaring.
 *
 * Transforms a program with macros into a macro-free program by inlining all macro calls.
 * This must be called AFTER type checking.
 */

/**
 * Inline all macro calls in a program, producing a macro-free AST.
 */
fun inlineMacros(program: GameAst): GameAst {
    if (program.macros.isEmpty()) {
        return program // No macros, nothing to inline
    }

    val macroEnv = program.macros.associateBy { it.name }

    return program.copy(
        macros = emptyList(),  // Drop all macros
        game = inlineMacrosInExt(program.game, macroEnv)
    )
}

/** Inline macros in Ext */
private fun inlineMacrosInExt(ext: Ext, macroEnv: Map<VarId, MacroDec>): Ext = when (ext) {
    is Ext.Bind -> ext.copy(
        qs = ext.qs.map { q ->
            q.copy(where = inlineMacrosInExp(q.where, macroEnv))
        },
        ext = inlineMacrosInExt(ext.ext, macroEnv)
    )

    is Ext.BindSingle -> ext.copy(
        q = ext.q.copy(where = inlineMacrosInExp(ext.q.where, macroEnv)),
        ext = inlineMacrosInExt(ext.ext, macroEnv)
    )

    is Ext.Value -> ext.copy(
        outcome = inlineMacrosInOutcome(ext.outcome, macroEnv)
    )
}

/** Inline macros in Outcome */
private fun inlineMacrosInOutcome(outcome: Outcome, macroEnv: Map<VarId, MacroDec>): Outcome = when (outcome) {
    is Outcome.Cond -> outcome.copy(
        cond = inlineMacrosInExp(outcome.cond, macroEnv),
        ifTrue = inlineMacrosInOutcome(outcome.ifTrue, macroEnv),
        ifFalse = inlineMacrosInOutcome(outcome.ifFalse, macroEnv)
    )

    is Outcome.Value -> outcome.copy(
        ts = outcome.ts.mapValues { (_, exp) ->
            inlineMacrosInExp(exp, macroEnv)
        }
    )

    is Outcome.Let -> outcome.copy(
        init = inlineMacrosInExp(outcome.init, macroEnv),
        outcome = inlineMacrosInOutcome(outcome.outcome, macroEnv)
    )
}

/** Inline macros in Exp - this is the core inlining logic */
private fun inlineMacrosInExp(exp: Exp, macroEnv: Map<VarId, MacroDec>): Exp = when (exp) {
    is Exp.Call -> {
        // First inline macros in arguments
        val inlinedArgs = exp.args.map { inlineMacrosInExp(it, macroEnv) }

        // Check if this is a macro call
        val macro = macroEnv[exp.target.id]
        if (macro != null) {
            // Inline the macro
            inlineMacroCall(macro, inlinedArgs, macroEnv)
        } else {
            // Not a macro (must be a built-in like alldiff)
            exp.copy(args = inlinedArgs)
        }
    }

    is Exp.UnOp -> exp.copy(
        operand = inlineMacrosInExp(exp.operand, macroEnv)
    )

    is Exp.BinOp -> exp.copy(
        left = inlineMacrosInExp(exp.left, macroEnv),
        right = inlineMacrosInExp(exp.right, macroEnv)
    )

    is Exp.Cond -> exp.copy(
        cond = inlineMacrosInExp(exp.cond, macroEnv),
        ifTrue = inlineMacrosInExp(exp.ifTrue, macroEnv),
        ifFalse = inlineMacrosInExp(exp.ifFalse, macroEnv)
    )

    is Exp.Let -> exp.copy(
        init = inlineMacrosInExp(exp.init, macroEnv),
        exp = inlineMacrosInExp(exp.exp, macroEnv)
    )

    // Leaves: no inlining needed
    is Exp.Var, is Exp.Field, is Exp.Const.Num, is Exp.Const.Bool,
    is Exp.Const.Address, Exp.Const.UNDEFINED -> exp
}

/**
 * Inline a macro call by substituting parameters with arguments.
 *
 * Given: macro f(x: T1, y: T2) = body
 * And call: f(e1, e2)
 *
 * Returns: body[x -> e1, y -> e2]
 */
private fun inlineMacroCall(
    macro: MacroDec,
    args: List<Exp>,
    macroEnv: Map<VarId, MacroDec>
): Exp {
    // Build substitution map
    val substitution = macro.params.zip(args).associate { (param, arg) ->
        param.name to arg
    }

    // Substitute parameters in macro body
    val inlinedBody = substituteParams(macro.body, substitution)

    // Recursively inline any macro calls in the inlined body
    // (handles transitive macro calls: macro g calls macro f)
    return inlineMacrosInExp(inlinedBody, macroEnv)
}

/**
 * Substitute parameters with arguments in an expression.
 *
 * This performs capture-avoiding substitution:
 * - Parameter references are replaced with arguments
 * - let! bindings that shadow parameters are handled correctly
 */
private fun substituteParams(exp: Exp, substitution: Map<VarId, Exp>): Exp = when (exp) {
    is Exp.Var -> {
        // Replace parameter reference with argument
        substitution[exp.id] ?: exp
    }

    is Exp.Call -> exp.copy(
        args = exp.args.map { substituteParams(it, substitution) }
    )

    is Exp.UnOp -> exp.copy(
        operand = substituteParams(exp.operand, substitution)
    )

    is Exp.BinOp -> exp.copy(
        left = substituteParams(exp.left, substitution),
        right = substituteParams(exp.right, substitution)
    )

    is Exp.Cond -> exp.copy(
        cond = substituteParams(exp.cond, substitution),
        ifTrue = substituteParams(exp.ifTrue, substitution),
        ifFalse = substituteParams(exp.ifFalse, substitution)
    )

    is Exp.Let -> {
        // Handle variable shadowing:
        // If the let! binding shadows a parameter, remove that parameter from substitution
        val newSubstitution = if (substitution.containsKey(exp.dec.v.id)) {
            substitution - exp.dec.v.id
        } else {
            substitution
        }

        exp.copy(
            init = substituteParams(exp.init, substitution), // init uses original substitution
            exp = substituteParams(exp.exp, newSubstitution)  // body uses shadowed substitution
        )
    }

    // Leaves: no substitution needed
    is Exp.Field, is Exp.Const.Num, is Exp.Const.Bool,
    is Exp.Const.Address, Exp.Const.UNDEFINED -> exp
}

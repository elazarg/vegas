package vegas.ir

import vegas.StaticError
import vegas.VarId
import vegas.frontend.Ast
import vegas.frontend.Exp
import vegas.frontend.Outcome
import vegas.frontend.Role
import vegas.frontend.SourceLoc
import vegas.frontend.VarDec

fun desugar(outcome: Outcome): Outcome.Value = desugar(outcome, listOf())

private fun <T : Ast> copySpan(to: T, from: Ast): T {
    SourceLoc.copy(to, from)
    return to
}

/**
 * Substitute a variable with an expression in an expression.
 * Used for let-desugaring in AST-level backends.
 */
private fun substituteVar(exp: Exp, varId: VarId, replacement: Exp): Exp {
    return when (exp) {
        is Exp.Var -> if (exp.id == varId) replacement else exp
        is Exp.Const -> exp
        is Exp.Field -> exp
        is Exp.UnOp -> copySpan(Exp.UnOp(exp.op, substituteVar(exp.operand, varId, replacement)), exp)
        is Exp.BinOp -> copySpan(Exp.BinOp(
            exp.op,
            substituteVar(exp.left, varId, replacement),
            substituteVar(exp.right, varId, replacement)
        ), exp)
        is Exp.Cond -> copySpan(Exp.Cond(
            substituteVar(exp.cond, varId, replacement),
            substituteVar(exp.ifTrue, varId, replacement),
            substituteVar(exp.ifFalse, varId, replacement)
        ), exp)
        is Exp.Call -> copySpan(Exp.Call(
            exp.target,
            exp.args.map { substituteVar(it, varId, replacement) }
        ), exp)
        is Exp.Let -> {
            val newInit = substituteVar(exp.init, varId, replacement)
            val newBody = if (exp.dec.v.id == varId) {
                exp.exp  // Shadowed - don't substitute
            } else {
                substituteVar(exp.exp, varId, replacement)
            }
            copySpan(Exp.Let(exp.dec, newInit, newBody), exp)
        }
    }
}

/**
 * Substitute a variable with an expression in an outcome.
 * Used for let-desugaring in AST-level backends.
 */
private fun substituteVarInOutcome(outcome: Outcome, varId: VarId, replacement: Exp): Outcome {
    return when (outcome) {
        is Outcome.Value -> copySpan(
            Outcome.Value(outcome.ts.mapValues { (_, exp) ->
                substituteVar(exp, varId, replacement)
            }),
            outcome
        )
        is Outcome.Cond -> copySpan(
            Outcome.Cond(
                substituteVar(outcome.cond, varId, replacement),
                substituteVarInOutcome(outcome.ifTrue, varId, replacement),
                substituteVarInOutcome(outcome.ifFalse, varId, replacement)
            ),
            outcome
        )
        is Outcome.Let -> {
            val newInit = substituteVar(outcome.init, varId, replacement)
            val newBody = if (outcome.dec.v.id == varId) {
                outcome.outcome  // Shadowed - don't substitute
            } else {
                substituteVarInOutcome(outcome.outcome, varId, replacement)
            }
            copySpan(Outcome.Let(outcome.dec, newInit, newBody), outcome)
        }
    }
}


/**
 * Desugar Outcome.Let and Outcome.Cond into Outcome.Value.
 *
 * NOTE: This function is used by AST-level backends (Scribble) and tests.
 * For IR compilation, ToIR.kt's desugarOutcome performs substitution-based
 * desugaring. This function also uses substitution to eliminate let bindings
 * without creating IR-level Exp.Let nodes.
 */
private fun desugar(outcome: Outcome, names: List<Pair<VarDec, Exp>>): Outcome.Value = when (outcome) {
    is Outcome.Value -> {
        // No accumulated bindings - just return the value
        outcome
    }

    is Outcome.Cond -> {
        val ifTrue = desugar(outcome.ifTrue, names).ts
        val ifFalse = desugar(outcome.ifFalse, names).ts
        fun safeGetRole(m: Map<Role, Exp>, role: Role): Exp {
            try {
                return m.getValue(role)
            } catch (_: NoSuchElementException) {
                throw StaticError("$role is not a role", role)
            }
        }

        val ts = ifTrue.keys.associateWith {
            copySpan(Exp.Cond(outcome.cond, safeGetRole(ifTrue, it), safeGetRole(ifFalse, it)), it)
        }
        copySpan(Outcome.Value(ts), outcome)
    }

    is Outcome.Let -> {
        // Substitute the variable with its initialization value throughout the body
        // let! x = init in outcome  ~~>  desugar(outcome[x := init])
        val outcomeWithSubstitution = substituteVarInOutcome(outcome.outcome, outcome.dec.v.id, outcome.init)
        desugar(outcomeWithSubstitution, names)
    }
}


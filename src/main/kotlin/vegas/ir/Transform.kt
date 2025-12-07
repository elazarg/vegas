package vegas.ir

import vegas.StaticError
import vegas.VarId
import vegas.frontend.Ast
import vegas.frontend.Exp
import vegas.frontend.Outcome
import vegas.frontend.Role
import vegas.frontend.SourceLoc
import vegas.frontend.VarDec
import java.util.concurrent.atomic.AtomicInteger

fun desugar(outcome: Outcome): Outcome.Value = desugar(outcome, listOf())

private fun <T : Ast> copySpan(to: T, from: Ast): T {
    SourceLoc.copy(to, from)
    return to
}

// Fresh variable counter for α-renaming
private val freshVarCounter = AtomicInteger(0)

/**
 * Generate a fresh variable name that doesn't clash with existing variables.
 */
private fun freshVar(base: String = "v"): VarId {
    return VarId("${base}_${freshVarCounter.getAndIncrement()}")
}

/**
 * Collect all free variables in an expression.
 * A variable is free if it appears but is not bound by an enclosing let.
 */
fun freeVars(exp: Exp): Set<VarId> {
    return when (exp) {
        is Exp.Var -> setOf(exp.id)
        is Exp.Const -> emptySet()
        is Exp.Field -> emptySet()
        is Exp.UnOp -> freeVars(exp.operand)
        is Exp.BinOp -> freeVars(exp.left) + freeVars(exp.right)
        is Exp.Cond -> freeVars(exp.cond) + freeVars(exp.ifTrue) + freeVars(exp.ifFalse)
        is Exp.Call -> exp.args.flatMap { freeVars(it) }.toSet()
        is Exp.Let -> {
            // Variables free in init, plus variables free in body excluding the bound variable
            freeVars(exp.init) + (freeVars(exp.exp) - exp.dec.v.id)
        }
    }
}

/**
 * Rename all occurrences of a variable in an expression.
 * This is a simple syntactic renaming, not substitution.
 */
fun renameVar(exp: Exp, from: VarId, to: VarId): Exp {
    return when (exp) {
        is Exp.Var -> if (exp.id == from) copySpan(Exp.Var(to), exp) else exp
        is Exp.Const -> exp
        is Exp.Field -> exp
        is Exp.UnOp -> copySpan(Exp.UnOp(exp.op, renameVar(exp.operand, from, to)), exp)
        is Exp.BinOp -> copySpan(Exp.BinOp(
            exp.op,
            renameVar(exp.left, from, to),
            renameVar(exp.right, from, to)
        ), exp)
        is Exp.Cond -> copySpan(Exp.Cond(
            renameVar(exp.cond, from, to),
            renameVar(exp.ifTrue, from, to),
            renameVar(exp.ifFalse, from, to)
        ), exp)
        is Exp.Call -> copySpan(Exp.Call(
            exp.target,
            exp.args.map { renameVar(it, from, to) }
        ), exp)
        is Exp.Let -> {
            val newDec = if (exp.dec.v.id == from) {
                VarDec(Exp.Var(to), exp.dec.type)
            } else {
                exp.dec
            }
            val newInit = renameVar(exp.init, from, to)
            val newBody = renameVar(exp.exp, from, to)
            copySpan(Exp.Let(newDec, newInit, newBody), exp)
        }
    }
}

/**
 * Rename all occurrences of a variable in an outcome.
 */
fun renameVarInOutcome(outcome: Outcome, from: VarId, to: VarId): Outcome {
    return when (outcome) {
        is Outcome.Value -> copySpan(
            Outcome.Value(outcome.ts.mapValues { (_, exp) ->
                renameVar(exp, from, to)
            }),
            outcome
        )
        is Outcome.Cond -> copySpan(
            Outcome.Cond(
                renameVar(outcome.cond, from, to),
                renameVarInOutcome(outcome.ifTrue, from, to),
                renameVarInOutcome(outcome.ifFalse, from, to)
            ),
            outcome
        )
        is Outcome.Let -> {
            val newDec = if (outcome.dec.v.id == from) {
                VarDec(Exp.Var(to), outcome.dec.type)
            } else {
                outcome.dec
            }
            val newInit = renameVar(outcome.init, from, to)
            val newBody = renameVarInOutcome(outcome.outcome, from, to)
            copySpan(Outcome.Let(newDec, newInit, newBody), outcome)
        }
    }
}

/**
 * Substitute a variable with an expression in an expression.
 * Used for let-desugaring across all backends.
 *
 * This implements full capture-avoiding substitution with α-renaming.
 * When substituting into a let-binding, if the bound variable would capture
 * a free variable in the replacement expression, we rename the binder first.
 */
fun substituteVar(exp: Exp, varId: VarId, replacement: Exp): Exp {
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

            // If the let binding shadows our variable, don't substitute in body
            if (exp.dec.v.id == varId) {
                copySpan(Exp.Let(exp.dec, newInit, exp.exp), exp)
            } else {
                // Check if the binder would capture free variables in replacement
                val freeInReplacement = freeVars(replacement)

                if (exp.dec.v.id in freeInReplacement) {
                    // α-rename: generate fresh variable to avoid capture
                    val fresh = freshVar(exp.dec.v.id.name)
                    val renamedBody = renameVar(exp.exp, exp.dec.v.id, fresh)
                    val newDec = VarDec(Exp.Var(fresh), exp.dec.type)
                    val newBody = substituteVar(renamedBody, varId, replacement)
                    copySpan(Exp.Let(newDec, newInit, newBody), exp)
                } else {
                    // No capture risk - substitute normally
                    val newBody = substituteVar(exp.exp, varId, replacement)
                    copySpan(Exp.Let(exp.dec, newInit, newBody), exp)
                }
            }
        }
    }
}

/**
 * Substitute a variable with an expression in an outcome.
 * Used for let-desugaring across all backends.
 *
 * This implements full capture-avoiding substitution with α-renaming.
 * When substituting into a let-binding, if the bound variable would capture
 * a free variable in the replacement expression, we rename the binder first.
 */
fun substituteVarInOutcome(outcome: Outcome, varId: VarId, replacement: Exp): Outcome {
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

            // If the let binding shadows our variable, don't substitute in body
            if (outcome.dec.v.id == varId) {
                copySpan(Outcome.Let(outcome.dec, newInit, outcome.outcome), outcome)
            } else {
                // Check if the binder would capture free variables in replacement
                val freeInReplacement = freeVars(replacement)

                if (outcome.dec.v.id in freeInReplacement) {
                    // α-rename: generate fresh variable to avoid capture
                    val fresh = freshVar(outcome.dec.v.id.name)
                    val renamedBody = renameVarInOutcome(outcome.outcome, outcome.dec.v.id, fresh)
                    val newDec = VarDec(Exp.Var(fresh), outcome.dec.type)
                    val newBody = substituteVarInOutcome(renamedBody, varId, replacement)
                    copySpan(Outcome.Let(newDec, newInit, newBody), outcome)
                } else {
                    // No capture risk - substitute normally
                    val newBody = substituteVarInOutcome(outcome.outcome, varId, replacement)
                    copySpan(Outcome.Let(outcome.dec, newInit, newBody), outcome)
                }
            }
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


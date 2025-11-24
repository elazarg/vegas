package vegas.ir

import vegas.StaticError
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


// TODO: FIX. let binding does not seem to happen
private fun desugar(outcome: Outcome, names: List<Pair<VarDec, Exp>>): Outcome.Value = when (outcome) {
    is Outcome.Value -> outcome.copy(ts = outcome.ts.mapValues { (_, exp) ->
        names.foldRight(exp) { (vd, init), acc -> copySpan(Exp.Let(vd, init, acc), outcome) }
    })

    is Outcome.Cond -> {
        val ifTrue = desugar(outcome.ifTrue).ts
        val ifFalse = desugar(outcome.ifFalse).ts
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

    is Outcome.Let -> desugar(outcome.outcome, names + Pair(outcome.dec, outcome.init))
}


package vegas.semantics

import vegas.RoleId
import vegas.StaticError
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.asInt

/**
 * What a role's audit deposit is sized from, in the role's analysis utility
 * ([GameIR.utilityOf]):
 *  - [lower] and [upper] bound its utility at every terminal history of the
 *    model, including quits and every chance outcome;
 *  - [exits] are its utilities at the terminal histories where it quit
 *    (empty if it can never quit);
 *  - [intendedLower] is its least utility at a terminal history where nobody
 *    quit (null if there is none).
 *
 * These are the quantities of VegasCore's sequential-equilibrium theorem
 * (`Vegas.Paper.intended_raw_sequentialEquilibrium_preserved`, hypotheses
 * `lower_le`, `le_upper` and `exitBelow` of `ClientSpec`), where the paper's
 * "default" is a quit and its exit utility is the utility of a role that quit.
 */
data class UtilityBounds(
    val lower: Int,
    val upper: Int,
    val exits: Set<Int>,
    val intendedLower: Int?,
) {
    /** The theorem's fixed exit utility, if the role can quit and it is fixed. */
    val exit: Int? get() = exits.singleOrNull()

    /**
     * The expected charge the audit must impose: `max(0, a, hi) - min(0, a, lo)`.
     * The 0 accounts for an instance that never finishes (aborted on chain,
     * where every role gets its deposit back).
     */
    val spread: Int
        get() = maxOf(0, upper, exit ?: 0) - minOf(0, lower, exit ?: 0)
}

/**
 * Each strategic role's [UtilityBounds] over every way the game can end.
 * Returns null when the game cannot be enumerated within [budget] terminal
 * histories (for example, unbounded integer parameters): such a game has no
 * finite raw interface, so the theorem does not apply to it.
 */
fun utilityBounds(game: GameIR, budget: Int = 200_000): Map<RoleId, UtilityBounds>? {
    val semantics = GameSemantics(game)
    val roles = game.payoffs.keys
    val low = mutableMapOf<RoleId, Int>()
    val high = mutableMapOf<RoleId, Int>()
    val exits = roles.associateWith { mutableSetOf<Int>() }
    val intendedLow = mutableMapOf<RoleId, Int>()
    var terminals = 0

    fun visit(config: Configuration): Boolean {
        if (config.isTerminal()) {
            if (++terminals > budget) return false
            val nobodyQuit = roles.none { config.history.quit(it) }
            for (role in roles) {
                // Utilities are the analyst's view: a private draw counts at its drawn value.
                val u = eval({ config.history.get(it).let { v -> if (v is Expr.Const.Hidden) v.inner else v } },
                    game.utilityOf(role)).asInt()
                low.merge(role, u, ::minOf)
                high.merge(role, u, ::maxOf)
                if (config.history.quit(role)) exits.getValue(role) += u
                if (nobodyQuit) intendedLow.merge(role, u, ::minOf)
            }
            return true
        }
        val moves = semantics.enabledMoves(config)
        val plays = moves.filterIsInstance<Label.Play>()
        // Roles in a frontier act in canonical order: their moves commute, so
        // expanding one role at a time reaches every outcome without permutations.
        val next = plays.firstOrNull()?.role?.let { role -> plays.filter { it.role == role } } ?: moves
        return next.all { visit(applyMove(config, it)) }
    }

    return try {
        if (!visit(Configuration.initial(game))) return null
        roles.filter { it in low }.associateWith {
            UtilityBounds(low.getValue(it), high.getValue(it), exits.getValue(it), intendedLow[it])
        }
    } catch (_: StaticError) {
        null
    } catch (_: IllegalStateException) {
        null
    }
}

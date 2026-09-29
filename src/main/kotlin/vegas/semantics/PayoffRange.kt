package vegas.semantics

import vegas.RoleId
import vegas.StaticError
import vegas.ir.GameIR
import vegas.ir.asInt

/** The least and greatest payout a role can receive. */
data class PayoutRange(val min: Int, val max: Int) {
    val width: Int get() = max - min
}

/**
 * Each role's payout range over every way the game can end: every terminal
 * history of the model, including quits and every chance outcome, plus an
 * aborted instance, where a role that joined gets its deposit back.
 *
 * This is the range VegasCore's deposit bound uses (`rosterAuditDeposit`):
 * any deviation's gain is at most the role's range. Returns null when the
 * game cannot be enumerated within [budget] terminal histories (for
 * example, unbounded integer parameters); callers then fall back to the pot.
 */
fun payoutRanges(game: GameIR, budget: Int = 200_000): Map<RoleId, PayoutRange>? {
    val semantics = GameSemantics(game)
    val roles = game.payoffs.keys
    val low = roles.associateWith { role -> game.dag.deposit(role).v }.toMutableMap()
    val high = low.toMutableMap()
    var terminals = 0

    fun visit(config: Configuration): Boolean {
        if (config.isTerminal()) {
            if (++terminals > budget) return false
            for (role in roles) {
                val payout = eval({ config.history.get(it) }, game.payoffs.getValue(role)).asInt()
                low[role] = minOf(low.getValue(role), payout)
                high[role] = maxOf(high.getValue(role), payout)
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
        if (visit(Configuration.initial(game))) roles.associateWith { PayoutRange(low.getValue(it), high.getValue(it)) } else null
    } catch (_: StaticError) {
        null
    } catch (_: IllegalStateException) {
        null
    }
}

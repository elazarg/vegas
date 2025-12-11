package vegas.backend.bitcoin

import vegas.RoleId
import vegas.ir.GameIR

/**
 * Generates a human-readable string representation of the LightningProtocol.
 * This serves as the "Object File" for the runtime and for Golden Master tests.
 */
fun generateLightningProtocol(game: GameIR, roleAStr: String, roleBStr: String, pot: Long): String {
    // Resolve RoleIds from string names
    val allRoles = game.roles.associateBy { it.name }
    val roleA = allRoles[roleAStr] ?: RoleId(roleAStr)
    val roleB = allRoles[roleBStr] ?: RoleId(roleBStr)

    val protocol = LightningCompiler.compile(game, roleA, roleB, pot)
    return protocol.toText()
}

private fun LightningProtocol.toText(): String = buildString {
    appendLine("LIGHTNING_PROTOCOL \"$name\"")
    appendLine("ROLES: A=${roleA.name}, B=${roleB.name}")
    appendLine("POT: $totalPot sat")
    appendLine("ROOT: $rootStateId")
    appendLine("STATES:")

    // Sort by ID for deterministic output
    states.toSortedMap().forEach { (_, state) ->
        appendLine(state.toText().prependIndent("  "))
    }
}

private fun ProtocolState.toText(): String = buildString {
    append("STATE $id")
    if (activePlayer == null) {
        append(" [TERMINAL]")
    } else {
        append(" [TURN: ${activePlayer.name}]")
    }
    appendLine()

    appendLine("  ABORT_BALANCE: A=${abortBalance.amountA}, B=${abortBalance.amountB}")

    if (transitions.isNotEmpty()) {
        appendLine("  TRANSITIONS:")
        // Sort transitions by label to ensure deterministic output
        transitions.sortedBy { it.label.toString() }.forEach { t ->
            appendLine("    -> ${t.nextStateId} via ${t.label}")
        }
    } else {
        appendLine("  TRANSITIONS: <NONE>")
    }
}

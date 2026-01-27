package vegas.eth

/**
 * Result of probing for an external tool.
 */
sealed class ToolStatus {
    data class Available(val path: String, val version: String) : ToolStatus()
    data class Missing(val reason: String) : ToolStatus()

    val isAvailable: Boolean get() = this is Available
}

/**
 * Probes for external tools required by Ethereum tests: `anvil` and `solc`.
 *
 * Results are cached per JVM to avoid repeated process spawns.
 * Used by test specs in `enabledIf` conditions.
 */
class ToolCheck private constructor(
    val anvil: ToolStatus,
    val solc: ToolStatus,
) {
    val allAvailable: Boolean get() = anvil.isAvailable && solc.isAvailable

    companion object {
        @Volatile
        private var instance: ToolCheck? = null

        /** Get or create a cached ToolCheck instance. */
        fun cached(): ToolCheck {
            return instance ?: synchronized(this) {
                instance ?: create().also { instance = it }
            }
        }

        private fun create(): ToolCheck {
            return ToolCheck(
                anvil = probeAnvil(),
                solc = probeSolc(),
            )
        }

        private fun probeAnvil(): ToolStatus {
            return try {
                val process = ProcessBuilder("anvil", "--version")
                    .redirectErrorStream(true)
                    .start()
                val output = process.inputStream.bufferedReader().readText().trim()
                val exitCode = process.waitFor()
                if (exitCode == 0 && output.isNotEmpty()) {
                    val version = output.lines().firstOrNull()?.trim() ?: output
                    ToolStatus.Available("anvil", version)
                } else {
                    ToolStatus.Missing("anvil returned exit code $exitCode")
                }
            } catch (_: Exception) {
                ToolStatus.Missing("anvil not found on PATH")
            }
        }

        private fun probeSolc(): ToolStatus {
            return try {
                val process = ProcessBuilder("solc", "--version")
                    .redirectErrorStream(true)
                    .start()
                val output = process.inputStream.bufferedReader().readText().trim()
                val exitCode = process.waitFor()
                if (exitCode != 0) {
                    return ToolStatus.Missing("solc returned exit code $exitCode")
                }
                // Parse version from output like "Version: 0.8.31+commit.abcdef"
                val versionLine = output.lines().find { it.startsWith("Version:") }
                val version = versionLine
                    ?.removePrefix("Version:")?.trim()
                    ?: output.lines().lastOrNull()?.trim()
                    ?: output

                // Check minimum version 0.8.x
                val versionMatch = Regex("""(\d+)\.(\d+)\.(\d+)""").find(version)
                if (versionMatch != null) {
                    val (major, minor, _) = versionMatch.destructured
                    if (major.toInt() == 0 && minor.toInt() < 8) {
                        return ToolStatus.Missing("solc 0.8.x required, found $version")
                    }
                }

                ToolStatus.Available("solc", version)
            } catch (_: Exception) {
                ToolStatus.Missing("solc not found on PATH")
            }
        }
    }
}

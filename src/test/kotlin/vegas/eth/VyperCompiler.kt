package vegas.eth

import java.io.File

/** Invokes the `vyper` compiler on generated Vyper source. */
object VyperCompiler {

    /**
     * The vyper executable: the project `.venv` first (see setup-eth-tools.py),
     * then PATH; null if neither works.
     */
    val path: String? by lazy {
        val isWindows = System.getProperty("os.name").lowercase().contains("win")
        val venv = File(if (isWindows) ".venv/Scripts/vyper.exe" else ".venv/bin/vyper")
        listOfNotNull(venv.takeIf { it.exists() }?.absolutePath, "vyper").firstOrNull { candidate ->
            try {
                val p = ProcessBuilder(candidate, "--version").redirectErrorStream(true).start()
                p.inputStream.bufferedReader().readText()
                p.waitFor() == 0
            } catch (_: Exception) {
                false
            }
        }
    }

    /** Compile [source]; returns the bytecode, or throws with the compiler's diagnostics. */
    fun compile(source: String, contractName: String): String {
        val vyper = path ?: error("vyper not found in project .venv or on PATH")
        val dir = File(System.getProperty("java.io.tmpdir"), "vegas-vyper").apply { mkdirs() }
        val file = File(dir, "$contractName.vy")
        file.writeText(source)
        val process = ProcessBuilder(vyper, file.absolutePath).redirectErrorStream(true).start()
        val output = process.inputStream.bufferedReader().readText()
        check(process.waitFor() == 0) { "vyper compilation of $contractName failed:\n$output" }
        return output.trim()
    }
}

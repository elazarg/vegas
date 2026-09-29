package vegas.eth

import java.io.File

/**
 * Foundry's `cast`, for transaction types `eth_sendTransaction` cannot build
 * (blob and set-code transactions). It lives next to the resolved anvil.
 */
object Cast {
    /** Private key of [AnvilNode.accounts]`[index]`, derived from the test mnemonic. */
    fun key(index: Int): String =
        run("wallet", "private-key", "--mnemonic", AnvilNode.MNEMONIC, "--mnemonic-index", index.toString())

    val path: String? by lazy {
        val anvil = ToolCheck.cached().anvilPath ?: return@lazy null
        val dir = File(anvil).parentFile ?: return@lazy null
        listOf("cast.exe", "cast").map { File(dir, it) }.firstOrNull { it.exists() }?.absolutePath
    }

    /** Run cast, answering yes to its confirmation prompts; returns its last output line. */
    fun run(vararg args: String): String {
        val process = ProcessBuilder(listOf(requireNotNull(path) { "cast not found next to anvil" }) + args)
            .redirectErrorStream(true).start()
        process.outputStream.bufferedWriter().use { it.write("y\n") }
        val output = process.inputStream.bufferedReader().readText()
        check(process.waitFor() == 0) { "cast ${args.joinToString(" ")} failed:\n$output" }
        return output.trim().lines().last().substringAfterLast(" ")
    }

    /**
     * Send a set-code (type 4) transaction; returns its hash. The gas limit is
     * explicit so a call that reverts is still sent (estimation would fail).
     */
    fun sendSetCode(rpcUrl: String, key: String, to: String, data: String, delegate: String): String =
        run("send", "--rpc-url", rpcUrl, "--private-key", key, "--auth", delegate, "--gas-limit", "300000",
            to, data, "--async")

    /** Send a blob (type 3) transaction carrying [blob]; returns its hash. */
    fun sendBlob(rpcUrl: String, key: String, to: String, data: String, blob: ByteArray): String {
        val file = File.createTempFile("vegas-blob", ".bin").apply { writeBytes(blob); deleteOnExit() }
        // Explicit gas and fees: estimation fails on a zero-fee node and for calls that revert.
        return run("send", "--rpc-url", rpcUrl, "--private-key", key, "--blob", "--path", file.absolutePath,
            "--gas-limit", "300000", "--blob-gas-price", "1", "--priority-gas-price", "1", "--gas-price", "2",
            to, data, "--async")
    }
}

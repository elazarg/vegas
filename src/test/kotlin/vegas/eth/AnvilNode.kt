package vegas.eth

import java.io.BufferedReader
import java.io.InputStreamReader
import java.net.URI
import java.net.http.HttpClient
import java.net.http.HttpRequest
import java.net.http.HttpResponse

/**
 * Manages a single `anvil` subprocess for Ethereum testing.
 *
 * Each test suite creates its own AnvilNode in beforeSpec/afterSpec.
 * Configuration is deterministic: fixed mnemonic + chainId, dynamic port.
 */
class AnvilNode {
    companion object {
        /** Standard test mnemonic — produces deterministic accounts. */
        const val MNEMONIC = "test test test test test test test test test test test junk"
        const val CHAIN_ID = 31337

        /**
         * Pre-funded accounts derived from the standard test mnemonic.
         * These are the first 10 accounts from the HD wallet.
         */
        val ACCOUNTS = listOf(
            "0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266",
            "0x70997970C51812dc3A010C7d01b50e0d17dc79C8",
            "0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC",
            "0x90F79bf6EB2c4f870365E785982E1f101E93b906",
            "0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65",
            "0xa0Ee7A142d267C1f36714E4a8F75612F20a79720",
            "0xBcd4042DE499D14e55001CcbB24a551F3b954096",
            "0x71bE63f3384f5fb98995898A86B02Fb2426c5788",
            "0xFABB0ac9d68B0B445fB7357272Ff202C5651694a",
            "0x1CBd3b2770909D4e10f157cABC84C7264073C9Ec",
        )
    }

    private var process: Process? = null
    private var drainThread: Thread? = null
    private var _rpcUrl: String? = null

    val rpcUrl: String get() = _rpcUrl ?: error("AnvilNode not started")
    val accounts: List<String> get() = ACCOUNTS

    /**
     * Start the anvil process.
     *
     * Uses port 0 (OS-assigned free port), parses actual port from stdout.
     * Performs a strict readiness probe via eth_chainId.
     *
     * @throws IllegalStateException if anvil doesn't respond within 5 seconds
     */
    fun start() {
        val pb = ProcessBuilder(
            "anvil",
            "--mnemonic", MNEMONIC,
            "--chain-id", CHAIN_ID.toString(),
            "--port", "0",  // OS-assigned port
            "--accounts", "10",
            "--balance", "10000",  // 10000 ETH per account
            "--base-fee", "0",    // Zero base fee for deterministic balance comparisons
            "--gas-price", "0",   // Zero gas price for legacy transactions
        ).redirectErrorStream(true)

        val proc = pb.start()
        process = proc

        // Parse port from anvil's stdout
        val reader = BufferedReader(InputStreamReader(proc.inputStream))
        val startTime = System.currentTimeMillis()
        var port: Int? = null

        while (System.currentTimeMillis() - startTime < 10_000) {
            if (!proc.isAlive) {
                val remaining = reader.readText()
                error("anvil process died during startup. Output: $remaining")
            }
            if (reader.ready()) {
                val line = reader.readLine() ?: continue
                // Look for "Listening on 127.0.0.1:NNNNN" or "Listening on 0.0.0.0:NNNNN"
                val match = Regex("""Listening on \S+:(\d+)""").find(line)
                if (match != null) {
                    port = match.groupValues[1].toInt()
                    break
                }
            } else {
                Thread.sleep(50)
            }
        }

        if (port == null) {
            proc.destroyForcibly()
            error("Failed to parse port from anvil output within 10 seconds")
        }

        _rpcUrl = "http://127.0.0.1:$port"

        // Drain anvil's stdout in background to prevent pipe buffer from filling up
        // (which would cause anvil to block on writes and freeze)
        drainThread = Thread({
            try {
                while (reader.readLine() != null) { /* discard */ }
            } catch (_: Exception) { /* process closed */ }
        }, "anvil-drain").apply {
            isDaemon = true
            start()
        }

        // Strict readiness probe: poll eth_chainId
        waitForReady()
    }

    private fun waitForReady() {
        val client = HttpClient.newHttpClient()
        val startTime = System.currentTimeMillis()

        while (System.currentTimeMillis() - startTime < 5_000) {
            try {
                val request = HttpRequest.newBuilder()
                    .uri(URI.create(rpcUrl))
                    .header("Content-Type", "application/json")
                    .POST(HttpRequest.BodyPublishers.ofString(
                        """{"jsonrpc":"2.0","method":"eth_chainId","params":[],"id":1}"""
                    ))
                    .build()

                val response = client.send(request, HttpResponse.BodyHandlers.ofString())
                if (response.statusCode() == 200 && response.body().contains("result")) {
                    return  // Anvil is ready
                }
            } catch (_: Exception) {
                // Connection refused — anvil not ready yet
            }
            Thread.sleep(50)
        }

        stop()
        error("anvil readiness probe timed out after 5 seconds at $rpcUrl")
    }

    /** Stop the anvil process. */
    fun stop() {
        process?.let { proc ->
            proc.destroyForcibly()
            proc.waitFor()
        }
        process = null
        drainThread?.interrupt()
        drainThread = null
        _rpcUrl = null
    }
}

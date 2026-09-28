package vegas.eth

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
    private var _rpcUrl: String? = null

    val rpcUrl: String get() = _rpcUrl ?: error("AnvilNode not started")
    val accounts: List<String> get() = ACCOUNTS

    /**
     * Start the anvil process.
     *
     * Listens on a free port chosen here; its output is discarded.
     * Performs a strict readiness probe via eth_chainId.
     *
     * @throws IllegalStateException if anvil doesn't respond within 10 seconds
     */
    fun start() {
        // Pick a free port here rather than parsing anvil's output: its output
        // is discarded by the OS, so no pipe can fill up and stall the node.
        val port = java.net.ServerSocket(0).use { it.localPort }
        val pb = ProcessBuilder(
            ToolCheck.cached().anvilPath ?: "anvil",
            "--mnemonic", MNEMONIC,
            "--chain-id", CHAIN_ID.toString(),
            "--port", port.toString(),
            "--accounts", "10",
            "--balance", "10000",  // 10000 ETH per account
            "--base-fee", "0",    // Zero base fee for deterministic balance comparisons
            "--gas-price", "0",   // Zero gas price for legacy transactions
        ).redirectErrorStream(true).redirectOutput(ProcessBuilder.Redirect.DISCARD)

        process = pb.start()
        _rpcUrl = "http://127.0.0.1:$port"

        // Strict readiness probe: poll eth_chainId
        waitForReady()
    }

    private fun waitForReady() {
        val client = HttpClient.newHttpClient()
        val startTime = System.currentTimeMillis()

        while (System.currentTimeMillis() - startTime < 10_000) {
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
        error("anvil readiness probe timed out after 10 seconds at $rpcUrl")
    }

    /** Stop the anvil process. */
    fun stop() {
        process?.let { proc ->
            proc.destroyForcibly()
            proc.waitFor()
        }
        process = null
        _rpcUrl = null
    }
}

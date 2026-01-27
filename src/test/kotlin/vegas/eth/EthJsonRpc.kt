package vegas.eth

import kotlinx.serialization.json.*
import java.math.BigInteger
import java.net.URI
import java.net.http.HttpClient
import java.net.http.HttpRequest
import java.net.http.HttpResponse
import java.time.Duration
import java.util.concurrent.atomic.AtomicLong

/**
 * Transaction receipt returned by [EthJsonRpc.sendAndWait].
 */
data class TxReceipt(
    val txHash: String,
    val blockNumber: Long,
    val gasUsed: Long,
    val status: Boolean,
    val logs: List<JsonObject>,
    val contractAddress: String?,
)

/**
 * Thrown when a transaction reverts on-chain.
 * Includes diagnostic information for debugging.
 */
class TxRevertedException(
    val txHash: String,
    val functionName: String,
    val from: String,
    val to: String?,
    val inputData: String,
    val revertReason: String,
) : RuntimeException(
    "Transaction reverted: $revertReason\n" +
    "  function: $functionName\n" +
    "  from: $from\n" +
    "  to: ${to ?: "(deploy)"}\n" +
    "  txHash: $txHash\n" +
    "  calldata: ${inputData.take(66)}${if (inputData.length > 66) "..." else ""}"
)

/**
 * Thin JSON-RPC client for Ethereum (targeting Anvil).
 *
 * Provides typed methods for common operations:
 * - Transaction sending with receipt waiting
 * - Static calls
 * - Balance queries
 * - Anvil-specific time manipulation
 */
class EthJsonRpc(private val rpcUrl: String) {
    private val client = HttpClient.newBuilder()
        .connectTimeout(Duration.ofSeconds(10))
        .build()
    private val nextId = AtomicLong(1)

    // ========== Core RPC ==========

    private fun call(method: String, params: JsonArray): JsonElement {
        val id = nextId.getAndIncrement()
        val body = buildJsonObject {
            put("jsonrpc", "2.0")
            put("method", method)
            put("params", params)
            put("id", id)
        }

        val request = HttpRequest.newBuilder()
            .uri(URI.create(rpcUrl))
            .header("Content-Type", "application/json")
            .timeout(Duration.ofSeconds(30))
            .POST(HttpRequest.BodyPublishers.ofString(body.toString()))
            .build()

        val response = client.send(request, HttpResponse.BodyHandlers.ofString())
        val json = Json.parseToJsonElement(response.body()).jsonObject

        val error = json["error"]
        if (error != null && error !is JsonNull) {
            val errorObj = error.jsonObject
            val message = errorObj["message"]?.jsonPrimitive?.contentOrNull ?: error.toString()
            val data = errorObj["data"]?.jsonPrimitive?.contentOrNull
            throw RuntimeException("RPC error ($method): $message${data?.let { " data=$it" } ?: ""}")
        }

        return json["result"] ?: JsonNull
    }

    // ========== Transaction Operations ==========

    /**
     * Send a transaction and wait for the receipt.
     *
     * On success: returns [TxReceipt].
     * On revert: throws [TxRevertedException] with full diagnostic context.
     *
     * @param from Sender address (must be unlocked in anvil)
     * @param to Contract address (null for deploy)
     * @param data Hex-encoded calldata
     * @param value Wei to send (hex-encoded)
     * @param functionName Human-readable function name for error messages
     */
    fun sendAndWait(
        from: String,
        to: String? = null,
        data: String = "0x",
        value: String = "0x0",
        functionName: String = "unknown",
    ): TxReceipt {
        val params = buildJsonObject {
            put("from", from)
            if (to != null) put("to", to)
            put("data", data)
            put("value", value)
            put("gas", "0x1000000")  // 16M gas — generous for testing
            put("gasPrice", "0x0")   // Zero gas cost for deterministic balance comparisons
        }

        val txHash = call("eth_sendTransaction", buildJsonArray { add(params) })
            .jsonPrimitive.content

        // Poll for receipt (anvil auto-mines, so typically immediate)
        var receipt: TxReceipt? = null
        for (_attempt in 0..50) {
            val result = call("eth_getTransactionReceipt", buildJsonArray { add(txHash) })
            if (result !is JsonNull) {
                val obj = result.jsonObject
                receipt = TxReceipt(
                    txHash = txHash,
                    blockNumber = obj["blockNumber"]!!.jsonPrimitive.content.hexToLong(),
                    gasUsed = obj["gasUsed"]!!.jsonPrimitive.content.hexToLong(),
                    status = obj["status"]!!.jsonPrimitive.content == "0x1",
                    logs = obj["logs"]?.jsonArray?.map { it.jsonObject } ?: emptyList(),
                    contractAddress = obj["contractAddress"]?.jsonPrimitive?.contentOrNull,
                )
                break
            }
            Thread.sleep(50)
        }

        if (receipt == null) {
            error("Transaction receipt not found after 50 polls: $txHash")
        }

        if (!receipt.status) {
            // Try to get revert reason via eth_call replay
            val revertReason = tryGetRevertReason(from, to, data, value)
            throw TxRevertedException(
                txHash = txHash,
                functionName = functionName,
                from = from,
                to = to,
                inputData = data,
                revertReason = revertReason,
            )
        }

        return receipt
    }

    private fun tryGetRevertReason(from: String, to: String?, data: String, value: String): String {
        return try {
            val params = buildJsonObject {
                put("from", from)
                if (to != null) put("to", to)
                put("data", data)
                put("value", value)
                put("gas", "0x1000000")
            }
            call("eth_call", buildJsonArray { add(params); add("latest") })
            "unknown (eth_call succeeded on replay)"
        } catch (e: RuntimeException) {
            val message = e.message ?: "unknown"
            // Extract revert reason from error message
            val revertMatch = Regex("""revert(?:ed with reason string '([^']+)'|: (.+))""", RegexOption.IGNORE_CASE)
                .find(message)
            revertMatch?.groupValues?.drop(1)?.firstOrNull { it.isNotEmpty() } ?: message
        }
    }

    // ========== Static Calls ==========

    /**
     * Make a static call (no state changes).
     * Returns the hex-encoded return data.
     */
    fun ethCall(from: String, to: String, data: String): String {
        val params = buildJsonObject {
            put("from", from)
            put("to", to)
            put("data", data)
        }
        return call("eth_call", buildJsonArray { add(params); add("latest") })
            .jsonPrimitive.content
    }

    // ========== Balance Queries ==========

    /** Get balance in wei (as BigInteger — may exceed Long). */
    fun getBalance(address: String): BigInteger {
        val result = call("eth_getBalance", buildJsonArray {
            add(address)
            add("latest")
        })
        return result.jsonPrimitive.content.hexToBigInteger()
    }

    // ========== Anvil-specific Methods ==========

    /** Advance block timestamp by `seconds`. */
    fun evmIncreaseTime(seconds: Long) {
        call("evm_increaseTime", buildJsonArray { add(seconds) })
    }

    /** Mine a block. */
    fun evmMine() {
        call("evm_mine", buildJsonArray {})
    }

    /** Advance time and mine a block. */
    fun advanceTime(seconds: Long) {
        evmIncreaseTime(seconds)
        evmMine()
    }
}

private fun String.hexToLong(): Long {
    return removePrefix("0x").toLong(16)
}

private fun String.hexToBigInteger(): BigInteger {
    return BigInteger(removePrefix("0x"), 16)
}

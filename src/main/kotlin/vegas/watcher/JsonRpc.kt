package vegas.watcher

import kotlinx.serialization.json.*
import org.bouncycastle.jcajce.provider.digest.Keccak
import java.math.BigInteger
import java.net.URI
import java.net.http.HttpClient
import java.net.http.HttpRequest
import java.net.http.HttpResponse
import java.time.Duration
import java.util.concurrent.atomic.AtomicLong

/** A minimal Ethereum JSON-RPC client. */
class JsonRpc(private val url: String) {
    // HTTP/1.1: JSON-RPC needs nothing more, and HTTP/2 upgrade negotiation
    // with some node servers can leave a request hanging.
    private val http = HttpClient.newBuilder()
        .version(HttpClient.Version.HTTP_1_1)
        .connectTimeout(Duration.ofSeconds(10))
        .build()
    private val ids = AtomicLong()

    class RpcError(message: String) : RuntimeException(message)

    fun call(method: String, vararg params: JsonElement): JsonElement {
        val body = buildJsonObject {
            put("jsonrpc", "2.0")
            put("id", ids.incrementAndGet())
            put("method", method)
            put("params", JsonArray(params.toList()))
        }
        val request = HttpRequest.newBuilder(URI.create(url))
            .header("Content-Type", "application/json")
            .timeout(Duration.ofSeconds(30))
            .POST(HttpRequest.BodyPublishers.ofString(body.toString()))
            .build()
        val response = Json.parseToJsonElement(http.send(request, HttpResponse.BodyHandlers.ofString()).body()).jsonObject
        response["error"]?.let { throw RpcError("$method: $it") }
        return response["result"] ?: JsonNull
    }

    fun blockNumber(): Long = quantity(call("eth_blockNumber"))

    fun block(number: Long): JsonObject? =
        call("eth_getBlockByNumber", JsonPrimitive(hex(number)), JsonPrimitive(true)) as? JsonObject

    /** Pending and queued transactions, as reported by `txpool_content`. */
    fun txpool(): List<JsonObject> {
        val content = call("txpool_content") as? JsonObject ?: return emptyList()
        return listOf("pending", "queued").flatMap { section ->
            (content[section] as? JsonObject)?.values.orEmpty()
                .flatMap { byNonce -> (byNonce as JsonObject).values.map { it.jsonObject } }
        }
    }

    fun ethCall(from: String, to: String, data: ByteArray): ByteArray =
        unhex(call("eth_call", buildJsonObject {
            put("from", from); put("to", to); put("data", hex(data))
        }, JsonPrimitive("latest")).jsonPrimitive.content)

    /** Send from an account the node signs for; returns the transaction hash. */
    fun send(from: String, to: String, data: ByteArray): String =
        call("eth_sendTransaction", buildJsonObject {
            put("from", from); put("to", to); put("data", hex(data))
        }).jsonPrimitive.content

    fun receiptStatus(hash: String): Boolean? =
        (call("eth_getTransactionReceipt", JsonPrimitive(hash)) as? JsonObject)
            ?.get("status")?.jsonPrimitive?.content?.let { it == "0x1" }

    /** Wait for inclusion; true if the transaction succeeded. */
    fun awaitReceipt(hash: String, attempts: Int = 600): Boolean {
        repeat(attempts) {
            receiptStatus(hash)?.let { return it }
            Thread.sleep(100)
        }
        error("no receipt for $hash")
    }

    companion object {
        fun quantity(e: JsonElement): Long = BigInteger(e.jsonPrimitive.content.removePrefix("0x").ifEmpty { "0" }, 16).toLong()
        fun hex(n: Long): String = "0x" + n.toString(16)
        fun hex(b: ByteArray): String = "0x" + b.joinToString("") { "%02x".format(it) }
        fun unhex(s: String): ByteArray = s.removePrefix("0x").let { h ->
            val padded = if (h.length % 2 == 1) "0$h" else h
            ByteArray(padded.length / 2) { padded.substring(2 * it, 2 * it + 2).toInt(16).toByte() }
        }
        fun keccak256(data: ByteArray): ByteArray = Keccak.Digest256().digest(data)
        fun selector(signature: String): ByteArray = keccak256(signature.toByteArray()).copyOf(4)
    }
}

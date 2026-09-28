package vegas.watcher

import kotlinx.serialization.json.*
import java.math.BigInteger

/**
 * A transaction as a node reports it (in a block or in its pool), reduced to
 * what an audit needs: its signer, the exact payload its signature covers, and
 * the signature. The signer does not have to be trusted: the contract recovers
 * it from the signature.
 *
 * Supported types: legacy (with or without EIP-155 replay protection), access
 * list (1) and dynamic fee (2). Blob (3) and set-code (4) transactions are not
 * encoded yet; [fromNode] returns null for them, and the watcher reports them
 * as a coverage gap rather than dropping them silently.
 */
data class SignedTransaction(
    val hash: String,
    val from: String,
    val unsignedPayload: ByteArray,
    val yParity: Int,
    val r: ByteArray,
    val s: ByteArray,
) {
    override fun equals(other: Any?) = other is SignedTransaction && hash == other.hash
    override fun hashCode() = hash.hashCode()

    companion object {
        private fun JsonObject.field(name: String): String? = (this[name] as? JsonPrimitive)?.contentOrNull

        private fun JsonObject.int(name: String): Rlp =
            Rlp.int(BigInteger(requireNotNull(field(name)) { "transaction has no $name" }.removePrefix("0x").ifEmpty { "0" }, 16))

        private fun JsonObject.bytes(name: String): Rlp = Rlp.Bytes(JsonRpc.unhex(field(name) ?: "0x"))

        private fun JsonObject.to(): Rlp = Rlp.Bytes(field("to")?.let { JsonRpc.unhex(it) } ?: ByteArray(0))

        private fun JsonObject.accessList(): Rlp = Rlp.Items((this["accessList"] as? JsonArray).orEmpty().map { entry ->
            val o = entry.jsonObject
            Rlp.Items(listOf(
                o.bytes("address"),
                Rlp.Items((o["storageKeys"] as? JsonArray).orEmpty().map { Rlp.Bytes(JsonRpc.unhex(it.jsonPrimitive.content)) }),
            ))
        })

        /** Rebuild the signed payload from a node's JSON view of a transaction. */
        fun fromNode(tx: JsonObject): SignedTransaction? {
            val type = tx.field("type")?.let { BigInteger(it.removePrefix("0x").ifEmpty { "0" }, 16).toInt() } ?: 0
            val common = listOf(tx.int("nonce"))
            val (payload, parity) = when (type) {
                0 -> {
                    val v = BigInteger(tx.field("v")!!.removePrefix("0x"), 16).toLong()
                    val base = common + listOf(tx.int("gasPrice"), tx.int("gas"), tx.to(), tx.int("value"), tx.bytes("input"))
                    if (v >= 35) {
                        val chainId = (v - 35) / 2
                        Rlp.Items(base + listOf(Rlp.int(chainId), Rlp.int(0), Rlp.int(0))).encode() to (v - 35 - 2 * chainId).toInt()
                    } else {
                        Rlp.Items(base).encode() to (v - 27).toInt()
                    }
                }
                1 -> byteArrayOf(1) + Rlp.Items(listOf(tx.int("chainId")) + common + listOf(
                    tx.int("gasPrice"), tx.int("gas"), tx.to(), tx.int("value"), tx.bytes("input"), tx.accessList(),
                )).encode() to parity(tx)
                2 -> byteArrayOf(2) + Rlp.Items(listOf(tx.int("chainId")) + common + listOf(
                    tx.int("maxPriorityFeePerGas"), tx.int("maxFeePerGas"), tx.int("gas"), tx.to(), tx.int("value"),
                    tx.bytes("input"), tx.accessList(),
                )).encode() to parity(tx)
                else -> return null
            }
            return SignedTransaction(
                hash = tx.field("hash")!!,
                from = tx.field("from")!!.lowercase(),
                unsignedPayload = payload,
                yParity = parity,
                r = word(tx.field("r")!!),
                s = word(tx.field("s")!!),
            )
        }

        private fun parity(tx: JsonObject): Int =
            BigInteger((tx.field("yParity") ?: tx.field("v")!!).removePrefix("0x").ifEmpty { "0" }, 16).toInt()

        private fun word(hex: String): ByteArray {
            val b = JsonRpc.unhex(hex).dropWhile { it == 0.toByte() }.toByteArray()
            return ByteArray(32 - b.size) + b
        }
    }
}

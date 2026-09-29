package vegas.watcher

import kotlinx.serialization.json.*
import java.math.BigInteger

/**
 * A transaction as a node reports it (in a block or in its pool), reduced to
 * what an audit needs: its signer, the exact payload its signature covers, and
 * the signature. The signer does not have to be trusted: the contract recovers
 * it from the signature.
 *
 * All five transaction types are encoded: legacy (with or without EIP-155
 * replay protection), access list (1), dynamic fee (2), blob (3) and set-code (4).
 */
data class SignedTransaction(
    val hash: String,
    val from: String,
    val type: Int,
    /** The transaction's own fields, in signing order, without replay-protection suffix or signature. */
    private val fields: List<Rlp>,
    /** For a legacy EIP-155 transaction, the chain id folded into the payload and `v`. */
    private val legacyChainId: Long?,
    val yParity: Int,
    val r: ByteArray,
    val s: ByteArray,
) {
    override fun equals(other: Any?) = other is SignedTransaction && hash == other.hash
    override fun hashCode() = hash.hashCode()

    private val prefix: ByteArray get() = if (type == 0) ByteArray(0) else byteArrayOf(type.toByte())

    /** The exact bytes the signature covers. */
    val unsignedPayload: ByteArray
        get() = prefix + Rlp.Items(
            fields + (legacyChainId?.let { listOf(Rlp.int(it), Rlp.int(0), Rlp.int(0)) } ?: emptyList())
        ).encode()

    /** The signed transaction as broadcast; its Keccak hash is the transaction hash. */
    val envelope: ByteArray
        get() {
            val v = when {
                type != 0 -> yParity.toLong()
                legacyChainId != null -> 35 + 2 * legacyChainId + yParity
                else -> 27L + yParity
            }
            return prefix + Rlp.Items(fields + listOf(Rlp.int(v), Rlp.int(BigInteger(1, r)), Rlp.int(BigInteger(1, s)))).encode()
        }

    companion object {
        private fun JsonObject.field(name: String): String? = (this[name] as? JsonPrimitive)?.contentOrNull

        private fun quantity(hex: String?): BigInteger =
            BigInteger(requireNotNull(hex) { "missing quantity" }.removePrefix("0x").ifEmpty { "0" }, 16)

        private fun JsonObject.int(name: String): Rlp = Rlp.int(quantity(field(name) ?: error("transaction has no $name")))

        private fun JsonObject.bytes(name: String): Rlp = Rlp.Bytes(JsonRpc.unhex(field(name) ?: "0x"))

        private fun JsonObject.to(): Rlp = Rlp.Bytes(field("to")?.let { JsonRpc.unhex(it) } ?: ByteArray(0))

        private fun JsonObject.accessList(): Rlp = Rlp.Items((this["accessList"] as? JsonArray).orEmpty().map { entry ->
            val o = entry.jsonObject
            Rlp.Items(listOf(
                o.bytes("address"),
                Rlp.Items((o["storageKeys"] as? JsonArray).orEmpty().map { Rlp.Bytes(JsonRpc.unhex(it.jsonPrimitive.content)) }),
            ))
        })

        private fun JsonObject.blobHashes(): Rlp = Rlp.Items((this["blobVersionedHashes"] as? JsonArray).orEmpty().map {
            Rlp.Bytes(JsonRpc.unhex(it.jsonPrimitive.content))
        })

        private fun JsonObject.authorizations(): Rlp = Rlp.Items((this["authorizationList"] as? JsonArray).orEmpty().map { entry ->
            val a = entry.jsonObject
            Rlp.Items(listOf(a.int("chainId"), a.bytes("address"), a.int("nonce"), a.int("yParity"), a.int("r"), a.int("s")))
        })

        /** Rebuild the transaction from a node's JSON view of it; null for an unknown type. */
        fun fromNode(tx: JsonObject): SignedTransaction? {
            val type = quantity(tx.field("type") ?: "0x0").toInt()
            fun dynamicFee() = listOf(tx.int("chainId"), tx.int("nonce"), tx.int("maxPriorityFeePerGas"), tx.int("maxFeePerGas"),
                tx.int("gas"), tx.to(), tx.int("value"), tx.bytes("input"), tx.accessList())
            var legacyChainId: Long? = null
            val (fields, parity) = when (type) {
                0 -> {
                    val v = quantity(tx.field("v")).toLong()
                    val base = listOf(tx.int("nonce"), tx.int("gasPrice"), tx.int("gas"), tx.to(), tx.int("value"), tx.bytes("input"))
                    if (v >= 35) {
                        legacyChainId = (v - 35) / 2
                        base to (v - 35 - 2 * legacyChainId).toInt()
                    } else {
                        base to (v - 27).toInt()
                    }
                }
                1 -> listOf(tx.int("chainId"), tx.int("nonce"), tx.int("gasPrice"), tx.int("gas"), tx.to(), tx.int("value"),
                    tx.bytes("input"), tx.accessList()) to parity(tx)
                2 -> dynamicFee() to parity(tx)
                3 -> dynamicFee() + listOf(tx.int("maxFeePerBlobGas"), tx.blobHashes()) to parity(tx)
                4 -> dynamicFee() + listOf(tx.authorizations()) to parity(tx)
                else -> return null
            }
            return SignedTransaction(
                hash = tx.field("hash")!!,
                from = tx.field("from")!!.lowercase(),
                type = type,
                fields = fields,
                legacyChainId = legacyChainId,
                yParity = parity,
                r = word(tx.field("r")!!),
                s = word(tx.field("s")!!),
            )
        }

        private fun parity(tx: JsonObject): Int = quantity(tx.field("yParity") ?: tx.field("v")).toInt()

        private fun word(hex: String): ByteArray {
            val b = JsonRpc.unhex(hex).dropWhile { it == 0.toByte() }.toByteArray()
            return ByteArray(32 - b.size) + b
        }
    }
}

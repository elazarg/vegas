package vegas.watcher

import kotlinx.serialization.json.JsonArray
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.JsonPrimitive
import java.math.BigInteger

/**
 * The watcher of an audited Vegas contract.
 *
 * It keeps every transaction signed by a game account that it sees, whether
 * in a block (included, successful or reverted) or only in a node's pool
 * (pending or queued, possibly never included). Once play has ended it asks
 * the contract to classify each record, alone and paired with each earlier
 * record of the same account, and submits the evidence the contract would
 * charge.
 *
 * The watcher is trusted only for coverage. It cannot frame a player: the
 * contract recovers the signer, and the readiness credential bound into every
 * move makes early moves self-evidently early. Its observation scope is the
 * chain plus the pools of the nodes in [pools]; a transaction that only ever
 * reaches other nodes, or is handed to an opponent off-chain, is outside it.
 *
 * @param rpc the node whose chain is audited and which receives reports.
 * @param roles the contract's strategic roles; their accounts are read from
 *   the contract's `address_<Role>()` getters once they join.
 * @param pools nodes whose pending and queued transactions are observed;
 *   more nodes (different peers, regions, private relays that expose their
 *   pool) cover more routes a deviator could choose.
 */
class Watcher(
    private val rpc: JsonRpc,
    private val contract: String,
    private val reporter: String,
    private val roles: List<String>,
    private val fromBlock: Long = 0,
    private val pools: List<JsonRpc> = listOf(rpc),
) {
    /** Game-account address (lowercase) to role. */
    private val accounts = mutableMapOf<String, String>()
    private val records = LinkedHashMap<String, SignedTransaction>()
    private val unencodable = LinkedHashSet<String>()
    private var nextBlock = fromBlock

    /** Every game-account transaction seen so far. */
    val recorded: Collection<SignedTransaction> get() = records.values

    /** Game-account transactions of an unknown type, which cannot be encoded: a coverage gap. */
    val unsupported: Set<String> get() = unencodable

    /** What happened to one record at audit time. */
    data class Outcome(val tx: SignedTransaction, val role: String, val charged: Boolean, val reason: String)

    /** Poll the chain and every observed pool once. */
    fun observe() {
        refreshAccounts()
        val latest = rpc.blockNumber()
        while (nextBlock <= latest) {
            val block = rpc.block(nextBlock) ?: break
            block["transactions"]?.let { txs -> (txs as JsonArray).forEach { keep(it as JsonObject) } }
            nextBlock++
        }
        pools.forEach { pool -> pool.txpool().forEach(::keep) }
    }

    private fun refreshAccounts() {
        for (role in roles) {
            if (accounts.containsValue(role)) continue
            val word = rpc.ethCall(reporter, contract, JsonRpc.selector("address_$role()"))
            val address = BigInteger(1, word)
            if (address.signum() != 0) accounts["0x" + address.toString(16).padStart(40, '0')] = role
        }
    }

    private fun keep(tx: JsonObject) {
        val from = (tx["from"] as? JsonPrimitive)?.content?.lowercase() ?: return
        if (from !in accounts) return
        val hash = (tx["hash"] as JsonPrimitive).content
        if (hash in records || hash in unencodable) return
        val signed = SignedTransaction.fromNode(tx)
        if (signed == null) unencodable += hash else records[hash] = signed
    }

    /** Whether the contract has seen play end, which opens the audit window. */
    fun playEnded(): Boolean = BigInteger(1, rpc.ethCall(reporter, contract, JsonRpc.selector("endedAt()"))).signum() != 0

    /**
     * Classify every record with the contract and submit the chargeable ones,
     * at most one per role (a role's audit deposit is burned once). A record
     * is chargeable alone when it is not a well-formed move of its signer's
     * node, or together with an earlier record of the same account when both
     * call the move of one node and differ beyond their fees.
     */
    fun audit(): List<Outcome> {
        observe()
        val charged = mutableSetOf<String>()
        val earlier = mutableMapOf<String, MutableList<SignedTransaction>>()
        return records.values.map { tx ->
            val role = accounts.getValue(tx.from)
            val calls = listOf(evidenceCall(tx)) + earlier[tx.from].orEmpty().map { pairCall(it, tx) }
            earlier.getOrPut(tx.from) { mutableListOf() } += tx
            val rejections = calls.map { call ->
                try {
                    rpc.ethCall(reporter, contract, call)
                    null
                } catch (e: JsonRpc.RpcError) {
                    e.message ?: "rejected"
                }
            }
            val accepted = calls.indices.firstOrNull { rejections[it] == null }
            when {
                accepted == null -> Outcome(tx, role, charged = false, reason = rejections.first()!!)
                role in charged -> Outcome(tx, role, charged = true, reason = "deposit already burned")
                else -> {
                    val hash = rpc.send(reporter, contract, calls[accepted])
                    check(rpc.awaitReceipt(hash)) { "report $hash for ${tx.hash} failed" }
                    charged += role
                    val what = if (accepted == 0) "reported" else "reported with an earlier transaction for its node"
                    Outcome(tx, role, charged = true, reason = "$what in $hash")
                }
            }
        }
    }

    /** ABI encoding of `report(bytes unsignedTx, bytes signature)`. */
    fun evidenceCall(tx: SignedTransaction): ByteArray =
        JsonRpc.selector("report(bytes,bytes)") + encodeBytes(listOf(tx.unsignedPayload, signature(tx)))

    /** ABI encoding of `reportPair(bytes first, bytes firstSignature, bytes second, bytes secondSignature)`. */
    fun pairCall(first: SignedTransaction, second: SignedTransaction): ByteArray =
        JsonRpc.selector("reportPair(bytes,bytes,bytes,bytes)") +
            encodeBytes(listOf(first.unsignedPayload, signature(first), second.unsignedPayload, signature(second)))

    /** `r`, `s` and the y-parity byte. */
    private fun signature(tx: SignedTransaction): ByteArray = tx.r + tx.s + byteArrayOf(tx.yParity.toByte())

    /** ABI encoding of a tuple of dynamic `bytes` arguments. */
    private fun encodeBytes(items: List<ByteArray>): ByteArray {
        fun word(n: Long) = BigInteger.valueOf(n).toByteArray().let { ByteArray(32 - it.size) + it }
        fun padded(b: ByteArray) = b + ByteArray((32 - b.size % 32) % 32)
        val heads = mutableListOf<ByteArray>()
        var offset = 32L * items.size
        for (item in items) {
            heads += word(offset)
            offset += 32 + padded(item).size
        }
        return (heads + items.flatMap { listOf(word(it.size.toLong()), padded(it)) }).reduce(ByteArray::plus)
    }
}

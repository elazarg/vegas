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
 * the contract to classify each record, and submits the ones the contract
 * would charge.
 *
 * The watcher is trusted only for coverage. It cannot frame a player: the
 * contract recovers the signer, and the readiness context bound into every
 * move makes early moves self-evidently early. Its observation scope is the
 * pools of the nodes it polls plus the chain; traffic handed to an opponent
 * through any other channel is outside it.
 *
 * @param roles the contract's strategic roles; their accounts are read from
 *   the contract's `address_<Role>()` getters once they join.
 */
class Watcher(
    private val rpc: JsonRpc,
    private val contract: String,
    private val reporter: String,
    private val roles: List<String>,
    private val fromBlock: Long = 0,
) {
    /** Game-account address (lowercase) to role. */
    private val accounts = mutableMapOf<String, String>()
    private val records = LinkedHashMap<String, SignedTransaction>()
    private val unencodable = LinkedHashSet<String>()
    private var nextBlock = fromBlock

    /** Every game-account transaction seen so far. */
    val recorded: Collection<SignedTransaction> get() = records.values

    /** Game-account transactions of a type the watcher cannot encode yet: a coverage gap. */
    val unsupported: Set<String> get() = unencodable

    /** What happened to one record at audit time. */
    data class Outcome(val tx: SignedTransaction, val role: String, val charged: Boolean, val reason: String)

    /** Poll the chain and the node's pool once. */
    fun observe() {
        refreshAccounts()
        val latest = rpc.blockNumber()
        while (nextBlock <= latest) {
            val block = rpc.block(nextBlock) ?: break
            block["transactions"]?.let { txs -> (txs as JsonArray).forEach { keep(it as JsonObject) } }
            nextBlock++
        }
        rpc.txpool().forEach(::keep)
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
     * at most one per role (a role's bond is burned once).
     */
    fun audit(): List<Outcome> {
        observe()
        val charged = mutableSetOf<String>()
        return records.values.map { tx ->
            val role = accounts.getValue(tx.from)
            val call = evidenceCall(tx)
            val reason = try {
                rpc.ethCall(reporter, contract, call)
                null
            } catch (e: JsonRpc.RpcError) {
                e.message ?: "rejected"
            }
            when {
                reason != null -> Outcome(tx, role, charged = false, reason = reason)
                role in charged -> Outcome(tx, role, charged = true, reason = "bond already burned")
                else -> {
                    val hash = rpc.send(reporter, contract, call)
                    check(rpc.awaitReceipt(hash)) { "report $hash for ${tx.hash} failed" }
                    charged += role
                    Outcome(tx, role, charged = true, reason = "reported in $hash")
                }
            }
        }
    }

    /** ABI encoding of `report(bytes unsignedTx, uint8 yParity, bytes32 r, bytes32 s)`. */
    fun evidenceCall(tx: SignedTransaction): ByteArray {
        fun word(n: Long) = BigInteger.valueOf(n).toByteArray().let { ByteArray(32 - it.size) + it }
        val payload = tx.unsignedPayload
        val padded = payload + ByteArray((32 - payload.size % 32) % 32)
        return JsonRpc.selector("report(bytes,uint8,bytes32,bytes32)") +
            word(4 * 32) + word(tx.yParity.toLong()) + tx.r + tx.s +
            word(payload.size.toLong()) + padded
    }
}

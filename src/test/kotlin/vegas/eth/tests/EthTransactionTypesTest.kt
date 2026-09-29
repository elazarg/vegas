package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.shouldBe
import kotlinx.serialization.json.JsonArray
import kotlinx.serialization.json.JsonPrimitive
import kotlinx.serialization.json.buildJsonObject
import kotlinx.serialization.json.put
import vegas.eth.*
import vegas.watcher.JsonRpc
import vegas.watcher.SignedTransaction

/**
 * The watcher rebuilds every transaction type exactly: the signed envelope
 * it reconstructs from the node's JSON hashes to the node's transaction hash.
 * (Its unsigned payload is the same field list without the signature.)
 */
@EnabledIf(EthToolsAvailable::class)
class EthTransactionTypesTest : FunSpec({
    val anvil = AnvilNode()
    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    val target = "0x0000000000000000000000000000000000000001"

    fun roundTrip(hash: String) {
        val tx = JsonRpc(anvil.rpcUrl).call("eth_getTransactionByHash", JsonPrimitive(hash)) as kotlinx.serialization.json.JsonObject
        val signed = requireNotNull(SignedTransaction.fromNode(tx))
        JsonRpc.hex(JsonRpc.keccak256(signed.envelope)) shouldBe hash
    }

    fun send(vararg fields: Pair<String, Any>): String = JsonRpc(anvil.rpcUrl).call("eth_sendTransaction", buildJsonObject {
        put("from", anvil.accounts[1]); put("to", target); put("data", "0x1234")
        for ((k, v) in fields) when (v) {
            is String -> put(k, v)
            is JsonArray -> put(k, v)
            else -> error("unsupported field $k")
        }
    }).let { (it as JsonPrimitive).content }

    test("legacy with replay protection") { roundTrip(send("type" to "0x0", "gasPrice" to "0x1")) }

    test("access list") {
        val list = kotlinx.serialization.json.Json.parseToJsonElement(
            """[{"address":"$target","storageKeys":["0x${"00".repeat(31)}01"]}]""") as JsonArray
        roundTrip(send("type" to "0x1", "gasPrice" to "0x1", "accessList" to list))
    }

    test("dynamic fee") { roundTrip(send("type" to "0x2")) }

    test("blob") {
        roundTrip(Cast.sendBlob(anvil.rpcUrl, Cast.key(2), target, "0x5678", "a blob".toByteArray()))
    }

    test("set code") {
        roundTrip(Cast.sendSetCode(anvil.rpcUrl, Cast.key(3), target, "0x9abc", "0x0000000000000000000000000000000000000abc"))
    }
})

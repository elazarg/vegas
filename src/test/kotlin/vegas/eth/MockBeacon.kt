package vegas.eth

import vegas.ir.Dist
import vegas.ir.Expr
import java.math.BigInteger

/**
 * A test double for the randomness beacon: the operator publishes the
 * output for a given request time. It stands in for a real beacon (drand,
 * a VRF service), whose outputs nobody chooses; here the test chooses them
 * so that chain draws can replay the model's chance outcomes.
 */
object MockBeacon {
    private val SOURCE = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.37;

        contract MockBeacon {
            address private immutable operator = msg.sender;
            mapping(uint256 => bytes32) public published;

            function publish(uint256 afterTimestamp, bytes32 value) external {
                require(msg.sender == operator, "not operator");
                published[afterTimestamp] = value;
            }

            // Like a real beacon, a round is available only once its time has come.
            function randomnessAfter(uint256 timestamp) external view returns (bytes32 value, uint256 roundTime) {
                if (block.timestamp <= timestamp) return (bytes32(0), 0);
                value = published[timestamp];
                roundTime = value == bytes32(0) ? 0 : timestamp + 1;
            }
        }
    """.trimIndent()

    fun deploy(rpc: EthJsonRpc, operator: String): String {
        val compiled = SolcCompiler.compile(SOURCE, "MockBeacon")
        return requireNotNull(rpc.sendAndWait(from = operator, data = compiled.bytecode).contractAddress)
    }

    fun publish(rpc: EthJsonRpc, operator: String, beacon: String, afterTimestamp: Long, output: ByteArray) {
        rpc.sendAndWait(
            from = operator,
            to = beacon,
            data = Hex.encode(AbiCodec.encodeCall(
                AbiCodec.functionSelector("publish(uint256,bytes32)"),
                AbiValue.Uint256(afterTimestamp), AbiValue.Bytes32(output),
            )),
            functionName = "publish",
        )
    }

    /**
     * A beacon output that the contract at [contract] maps to [value] at
     * schedule position [node]. This reimplements the contract's reduction
     * independently: `uint256(keccak256(abi.encode(output, contract, node))) mod D`
     * selects the value whose cumulative integer weight interval contains it.
     */
    fun outputDrawing(contract: String, node: Int, dist: Dist, value: Expr.Const): ByteArray {
        val denominator = dist.support.fold(BigInteger.ONE) { acc, (_, w) ->
            val d = BigInteger.valueOf(w.denominator.toLong()).abs()
            acc / acc.gcd(d) * d
        }
        val upper = dist.support.map { (_, w) ->
            BigInteger.valueOf(w.numerator.toLong()).abs() * (denominator / BigInteger.valueOf(w.denominator.toLong()).abs())
        }.runningReduce { a, b -> a + b }
        val k = dist.values.indexOf(value)
        require(k >= 0) { "$value is not in the support of $dist" }
        val lower = if (k == 0) BigInteger.ZERO else upper[k - 1]
        for (counter in 0L until 10_000L) {
            val output = AbiCodec.keccak256(AbiCodec.encodeUint256(counter))
            val seed = AbiCodec.keccak256(output + AbiCodec.encodeAddress(contract) + AbiCodec.encodeUint256(node.toLong()))
            val r = BigInteger(1, seed).mod(denominator)
            if (r >= lower && r < upper[k]) return output
        }
        error("no beacon output maps to $value")
    }
}

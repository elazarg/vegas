package vegas.eth

import java.math.BigInteger
import java.security.SecureRandom

/**
 * Manages commit-reveal protocol for hidden values.
 *
 * Computes commitment hashes that match Solidity's `_commitmentHash`:
 * ```
 * keccak256(abi.encode(COMMIT_TAG, address(this), role, actor, keccak256(abi.encode(value, salt))))
 * ```
 *
 * The commitment binds: tag + contract address + role enum value + actor address + payload hash.
 */
object CommitmentManager {

    /** Must match Solidity: keccak256("VEGAS_COMMIT_V1") */
    val COMMIT_TAG: ByteArray = AbiCodec.keccak256("VEGAS_COMMIT_V1")

    private val random = SecureRandom()

    /** Generate a random 256-bit salt. */
    fun generateSalt(): Long {
        return random.nextLong() and Long.MAX_VALUE  // keep positive
    }

    /**
     * Compute the commitment hash matching Solidity's `_commitmentHash`.
     *
     * @param contractAddress The deployed contract address
     * @param roleEnumValue The numeric value of the Role enum (e.g., A=1, B=2)
     * @param actorAddress The address of the committer (msg.sender)
     * @param payload ABI-encoded (value, salt) — same encoding as Solidity's abi.encode
     */
    fun commitmentHash(
        contractAddress: String,
        roleEnumValue: Int,
        actorAddress: String,
        payload: ByteArray,
    ): ByteArray {
        val payloadHash = AbiCodec.keccak256(payload)

        // abi.encode(COMMIT_TAG, address(this), role, actor, keccak256(payload))
        // In Solidity, addresses are left-padded to 32 bytes (same as uint160)
        val encoded = AbiCodec.encode(
            AbiValue.Bytes32(COMMIT_TAG),
            AbiValue.Bytes32(addressToBytes32(contractAddress)),
            AbiValue.Bytes32(intToBytes32(roleEnumValue)),
            AbiValue.Bytes32(addressToBytes32(actorAddress)),
            AbiValue.Bytes32(payloadHash),
        )

        return AbiCodec.keccak256(encoded)
    }

    /**
     * Build the ABI-encoded payload for abi.encode(value, salt).
     */
    fun encodePayload(vararg values: AbiValue): ByteArray =
        AbiCodec.encode(*values)
}

/** Convert an Ethereum address to a 32-byte left-padded representation. */
private fun addressToBytes32(address: String): ByteArray {
    val clean = address.removePrefix("0x")
    val addressBytes = BigInteger(clean, 16).toByteArray()
    val result = ByteArray(32)
    // Copy right-aligned
    val srcOffset = maxOf(0, addressBytes.size - 32)
    val destOffset = maxOf(0, 32 - addressBytes.size)
    val length = minOf(addressBytes.size, 32)
    System.arraycopy(addressBytes, srcOffset, result, destOffset, length)
    return result
}

/** Convert an int to a 32-byte big-endian representation. */
private fun intToBytes32(value: Int): ByteArray {
    return AbiCodec.encodeInt256(value)
}

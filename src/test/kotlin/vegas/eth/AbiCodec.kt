package vegas.eth

import org.bouncycastle.jcajce.provider.digest.Keccak
import java.math.BigInteger

/**
 * ABI encoding/decoding for the types Vegas generates.
 *
 * Implements Solidity ABI encoding for:
 * - int256, uint256: 32-byte sign-extended / zero-padded
 * - bool: 32-byte (0 or 1)
 * - bytes32: 32-byte raw
 *
 * Also provides keccak256 hashing and function selector computation.
 */
object AbiCodec {

    // ========== Keccak256 ==========

    /** Compute keccak256 hash of raw bytes. */
    fun keccak256(data: ByteArray): ByteArray {
        val digest = Keccak.Digest256()
        return digest.digest(data)
    }

    /** Compute keccak256 hash of a UTF-8 string. */
    fun keccak256(text: String): ByteArray = keccak256(text.toByteArray(Charsets.UTF_8))

    // ========== Function Selectors ==========

    /** Compute the 4-byte function selector: keccak256(signature)[0:4]. */
    fun functionSelector(signature: String): ByteArray =
        keccak256(signature).copyOfRange(0, 4)

    // ========== Value Encoding ==========

    /** Encode an int256 value as 32 bytes (two's complement, big-endian). */
    fun encodeInt256(value: Int): ByteArray = encodeInt256(value.toLong())

    fun encodeInt256(value: Long): ByteArray {
        val big = BigInteger.valueOf(value)
        return bigIntToBytes32(big)
    }

    /** Encode a uint256 value as 32 bytes (zero-padded, big-endian). */
    fun encodeUint256(value: Long): ByteArray {
        require(value >= 0) { "uint256 cannot be negative: $value" }
        return bigIntToBytes32(BigInteger.valueOf(value))
    }

    /** Encode a boolean as 32 bytes (0 or 1). */
    fun encodeBool(value: Boolean): ByteArray =
        encodeUint256(if (value) 1L else 0L)

    /** Encode raw bytes32 (must be exactly 32 bytes). */
    fun encodeBytes32(value: ByteArray): ByteArray {
        require(value.size == 32) { "bytes32 must be exactly 32 bytes, got ${value.size}" }
        return value.copyOf()
    }

    // ========== ABI Encode (multiple values) ==========

    /**
     * ABI-encode a list of typed values.
     * Each value is encoded as 32 bytes and concatenated.
     */
    fun encode(vararg values: AbiValue): ByteArray {
        return values.fold(ByteArray(0)) { acc, v -> acc + v.encode() }
    }

    /**
     * Build calldata: 4-byte selector + ABI-encoded arguments.
     */
    fun encodeCall(selector: ByteArray, vararg args: AbiValue): ByteArray {
        return selector + encode(*args)
    }

    // ========== Helpers ==========

    private fun bigIntToBytes32(value: BigInteger): ByteArray {
        val bytes = value.toByteArray()
        val result = ByteArray(32)
        if (value.signum() < 0) {
            // Fill with 0xFF for negative numbers (two's complement)
            result.fill(0xFF.toByte())
        }
        // Copy bytes right-aligned
        val srcOffset = maxOf(0, bytes.size - 32)
        val destOffset = maxOf(0, 32 - bytes.size)
        val length = minOf(bytes.size, 32)
        System.arraycopy(bytes, srcOffset, result, destOffset, length)
        return result
    }
}

/** Typed ABI value for encoding. */
sealed class AbiValue {
    abstract fun encode(): ByteArray

    data class Int256(val value: Int) : AbiValue() {
        override fun encode(): ByteArray = AbiCodec.encodeInt256(value)
    }

    data class Uint256(val value: Long) : AbiValue() {
        override fun encode(): ByteArray = AbiCodec.encodeUint256(value)
    }

    data class Bool(val value: Boolean) : AbiValue() {
        override fun encode(): ByteArray = AbiCodec.encodeBool(value)
    }

    data class Bytes32(val value: ByteArray) : AbiValue() {
        override fun encode(): ByteArray = AbiCodec.encodeBytes32(value)
        override fun equals(other: Any?): Boolean = other is Bytes32 && value.contentEquals(other.value)
        override fun hashCode(): Int = value.contentHashCode()
    }
}

/** Hex encoding/decoding utilities. */
object Hex {
    fun encode(bytes: ByteArray): String =
        "0x" + bytes.joinToString("") { "%02x".format(it) }

}

package vegas.watcher

import java.io.ByteArrayOutputStream
import java.math.BigInteger

/** An RLP value: a byte string or a list. */
sealed class Rlp {
    data class Bytes(val value: ByteArray) : Rlp() {
        override fun equals(other: Any?) = other is Bytes && value.contentEquals(other.value)
        override fun hashCode() = value.contentHashCode()
    }

    data class Items(val items: List<Rlp>) : Rlp()

    fun encode(): ByteArray = when (this) {
        is Bytes ->
            if (value.size == 1 && value[0].toInt() and 0xff < 0x80) value
            else header(0x80, value.size) + value
        is Items -> {
            val body = ByteArrayOutputStream().apply { items.forEach { write(it.encode()) } }.toByteArray()
            header(0xc0, body.size) + body
        }
    }

    companion object {
        /** A non-negative integer: big-endian, no leading zeros, zero as the empty string. */
        fun int(value: BigInteger): Rlp {
            require(value.signum() >= 0) { "RLP integers are non-negative" }
            val bytes = value.toByteArray().dropWhile { it == 0.toByte() }.toByteArray()
            return Bytes(bytes)
        }

        fun int(value: Long): Rlp = int(BigInteger.valueOf(value))

        private fun header(base: Int, length: Int): ByteArray =
            if (length < 56) byteArrayOf((base + length).toByte())
            else {
                val len = BigInteger.valueOf(length.toLong()).toByteArray().dropWhile { it == 0.toByte() }.toByteArray()
                byteArrayOf((base + 55 + len.size).toByte()) + len
            }
    }
}

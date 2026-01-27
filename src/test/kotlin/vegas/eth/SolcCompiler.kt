package vegas.eth

import kotlinx.serialization.json.*
import java.io.File

/**
 * Result of compiling a Solidity source file.
 *
 * @property abi The ABI as a JSON string
 * @property bytecode The deployment bytecode (hex-encoded, with 0x prefix)
 */
data class CompiledContract(
    val abi: String,
    val bytecode: String,
    val contractName: String,
)

/**
 * Invokes `solc --combined-json abi,bin` on generated Solidity source.
 * Parses bytecode + ABI from the output.
 */
object SolcCompiler {

    /**
     * Compile Solidity source code and return the compiled contract.
     *
     * @param source The Solidity source code
     * @param contractName The expected contract name (e.g., "Prisoners")
     * @return Compiled contract with ABI and bytecode
     * @throws IllegalStateException if compilation fails
     */
    fun compile(source: String, contractName: String): CompiledContract {
        // Write source to a temp file
        val tempDir = File(System.getProperty("java.io.tmpdir"), "vegas-solc")
        tempDir.mkdirs()
        val sourceFile = File(tempDir, "$contractName.sol")
        sourceFile.writeText(source)

        try {
            val process = ProcessBuilder(
                "solc",
                "--combined-json", "abi,bin",
                "--via-ir",
                "--optimize",
                sourceFile.absolutePath
            )
                .redirectErrorStream(false)
                .start()

            val stdout = process.inputStream.bufferedReader().readText()
            val stderr = process.errorStream.bufferedReader().readText()
            val exitCode = process.waitFor()

            if (exitCode != 0) {
                error("solc compilation failed (exit $exitCode):\n$stderr\n\nSource:\n$source")
            }

            // Parse the combined JSON output
            val json = Json.parseToJsonElement(stdout).jsonObject
            val contracts = json["contracts"]?.jsonObject
                ?: error("solc output missing 'contracts' key")

            // The key is "filepath:ContractName"
            val contractKey = contracts.keys.find { it.endsWith(":$contractName") }
                ?: error("Contract '$contractName' not found in solc output. Available: ${contracts.keys}")

            val contractJson = contracts[contractKey]!!.jsonObject
            val abi = contractJson["abi"]?.toString()
                ?: error("Missing ABI for $contractName")
            val bin = contractJson["bin"]?.jsonPrimitive?.content
                ?: error("Missing bytecode for $contractName")

            require(bin.isNotEmpty()) { "Empty bytecode for $contractName — is the contract abstract?" }

            return CompiledContract(
                abi = abi,
                bytecode = "0x$bin",
                contractName = contractName,
            )
        } finally {
            sourceFile.delete()
        }
    }
}

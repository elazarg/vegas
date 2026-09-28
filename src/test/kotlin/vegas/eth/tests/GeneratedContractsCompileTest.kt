package vegas.eth.tests

import io.kotest.core.annotation.Condition
import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.Spec
import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.backend.evm.generateVyper
import vegas.eth.SolcCompiler
import vegas.eth.ToolCheck
import vegas.eth.VyperCompiler
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import java.io.File
import kotlin.reflect.KClass

class SolcAvailable : Condition {
    override fun evaluate(kclass: KClass<out Spec>): Boolean = ToolCheck.cached().solcPath != null
}

class VyperAvailable : Condition {
    override fun evaluate(kclass: KClass<out Spec>): Boolean = VyperCompiler.path != null
}

/**
 * Every example's generated contract must be accepted by the real compiler,
 * not only the ones that have golden masters or on-chain traces.
 */
private val examples = File("examples").listFiles { f -> f.extension == "vg" }!!
    .map { it.nameWithoutExtension }.sorted()

private fun evmOf(name: String) = compileToEvm(compileToIR(inlineMacros(parseExample(name))))

@EnabledIf(SolcAvailable::class)
class GeneratedSolidityCompileTest : FreeSpec({
    "Solidity for every example compiles" - {
        withData(examples) { name ->
            val evm = evmOf(name)
            SolcCompiler.compile(generateSolidity(evm), evm.name)
        }
    }
})

@EnabledIf(VyperAvailable::class)
class GeneratedVyperCompileTest : FreeSpec({
    "Vyper for every example compiles" - {
        withData(examples) { name ->
            val evm = evmOf(name)
            VyperCompiler.compile(generateVyper(evm), evm.name)
        }
    }
})

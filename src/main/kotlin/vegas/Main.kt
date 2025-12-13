package vegas

import vegas.backend.scribble.genScribbleFromIR
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.backend.smt.generateSMT
import vegas.backend.smt.generateDQBF
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.backend.evm.generateVyper
import vegas.frontend.parseFile
import vegas.frontend.GameAst
import vegas.frontend.findRoleIds
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import java.nio.file.Paths
import java.nio.file.Files
import java.nio.file.Path
import kotlin.system.exitProcess

private fun doTypecheck(program: GameAst) {
    try {
        typeCheck(program)
    } catch (ex: NotImplementedError) {
        println(ex.message)
    } catch (ex: StaticError) {
        println("Type error: " + ex.message + " at " + ex.span())
    }
}

private fun writeFile(filename: String, f: () -> String) {
    print("Writing file $filename... ")
    try {
        val text = f()
        Paths.get(filename).toFile().writeText(text)
    } catch (ex: NotImplementedError) {
        println(ex.message)
    }
    println("Done")
}

private data class Outputs(
    val z3: Boolean,
    val dqbf: Boolean,
    val coalition: Set<String>?,
    val efg: Boolean,
    val scr: Boolean,
    val sol: Boolean,
    val vyper: Boolean
)

private fun parseOutputs(flags: List<String>): Outputs {
    // If empty, generate everything except possibly DQBF specific configs
    if (flags.isEmpty()) return Outputs(z3 = true, dqbf = false, coalition = null, efg = true, scr = true, sol = true, vyper = true)

    var wantZ3 = false
    var wantDqbf = false
    var coalition: Set<String>? = null
    var wantEfg = false
    var wantScr = false
    var wantSol = false
    var wantVyper = false

    var i = 0
    while (i < flags.size) {
        val f = flags[i]
        when (f.lowercase()) {
            "--z3" -> wantZ3 = true
            "--dqbf" -> wantDqbf = true
            "--coalition" -> {
                if (i + 1 < flags.size) {
                    coalition = flags[i + 1].split(",").map { it.trim() }.toSet()
                    i++
                } else {
                    throw IllegalArgumentException("--coalition requires an argument")
                }
            }
            "--efg" -> wantEfg = true
            "--scr" -> wantScr = true
            "--sol" -> wantSol = true
            "--vyper" -> wantVyper = true
            else -> throw IllegalArgumentException("Unknown flag: $f")
        }
        i++
    }

    // If the user provided any known output flags, emit only those.
    val any = wantZ3 || wantDqbf || wantEfg || wantScr || wantSol || wantVyper
    return if (any) Outputs(wantZ3, wantDqbf, coalition, wantEfg, wantScr, wantSol, wantVyper)
    else Outputs(z3 = true, dqbf = false, coalition = null, efg = true, scr = true, sol = true, vyper = true)
}

private fun runFile(inputPath: Path, outputs: Outputs) {
    require(Files.exists(inputPath)) { "Input file does not exist: $inputPath" }
    require(inputPath.toString().endsWith(".vg")) { "Expected a .vg file: $inputPath" }

    val baseName = inputPath.fileName.toString().removeSuffix(".vg")
    val outDir = inputPath.parent ?: Path.of(".")
    val outZ3 = outDir.resolve("$baseName.z3")
    val outDqbf = outDir.resolve("$baseName.dqbf.z3")
    val outEfg = outDir.resolve("$baseName.efg")
    val outScr = outDir.resolve("$baseName.scr")
    val outSol = outDir.resolve("$baseName.sol")
    val outVyper = outDir.resolve("$baseName.vy")

    println("Analyzing $inputPath ...")
    val program = parseFile(inputPath.toString()).copy(name = baseName, desc = baseName)

    println("roles: " + findRoleIds(program.game))
    doTypecheck(program)  // Type check the surface syntax (with macros)
    val inlined = inlineMacros(program)  // Inline macros (desugar)
    val ir = compileToIR(inlined)  // Compile inlined program to IR

    if (outputs.z3) writeFile(outZ3.toString()) { generateSMT(ir) }

    if (outputs.dqbf) {
        val coalitionSet = outputs.coalition?.map { RoleId.of(it) }?.toSet()
        writeFile(outDqbf.toString()) { generateDQBF(ir, coalitionSet) }
    }

    if (outputs.efg) writeFile(outEfg.toString()) { generateExtensiveFormGame(ir) }
    if (outputs.scr) writeFile(outScr.toString()) { genScribbleFromIR(ir) }

    // EVM backends use common IR
    val evmIr = if (outputs.sol || outputs.vyper) compileToEvm(ir) else null
    if (outputs.sol) writeFile(outSol.toString()) { generateSolidity(evmIr!!) }
    if (outputs.vyper) writeFile(outVyper.toString()) { generateVyper(evmIr!!) }

    println("Done")
    println()
}

fun main(args: Array<String>) {
    if (args.isEmpty()) {
        System.err.println(
            """
            Usage: vegas <path/to/file.vg> [--efg] [--z3] [--dqbf] [--coalition Role1,Role2] [--scr] [--sol] [--vyper]

            If no format flags are given, all standard outputs (excluding experimental DQBF) are generated alongside the input:
              - <file>.z3   (SMT)
              - <file>.efg  (Gambit EFG)
              - <file>.scr  (Scribble)
              - <file>.sol  (Solidity)
              - <file>.vy   (Vyper)
            """.trimIndent()
        )
        exitProcess(2)
    }

    val input = Path.of(args[0]).toAbsolutePath().normalize()
    val flags = args.drop(1)
    val outputs = try {
        parseOutputs(flags)
    } catch (e: IllegalArgumentException) {
        System.err.println("Error: ${e.message}")
        exitProcess(2)
    }

    try {
        runFile(input, outputs)
    } catch (e: Throwable) {
        System.err.println("Error: ${e.message}")
        e.printStackTrace()
        exitProcess(1)
    }
}

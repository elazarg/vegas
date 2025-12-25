package vegas.frontend

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import java.net.URI
import java.nio.file.Paths


fun parseCode(code: String, uri: URI = URI.create("inmemory:repl.vg")): GameAst {
    // Ensure there's always a withdraw statement
    var fullCode = if (!code.contains("withdraw")) "$code; withdraw {}" else code

    // Auto-wrap with game main() {} if not already present
    if (!fullCode.trim().startsWith("game ") && !fullCode.contains("game ")) {
        // Split into lines and separate type/macro declarations from game code
        val lines = fullCode.lines()
        val typeMacro = mutableListOf<String>()
        val gameCode = mutableListOf<String>()
        var inTypeMacro = false

        for (line in lines) {
            val trimmed = line.trim()
            when {
                trimmed.startsWith("type ") || trimmed.startsWith("macro ") -> {
                    inTypeMacro = true
                    typeMacro.add(line)
                    if (trimmed.endsWith(";")) inTypeMacro = false
                }
                inTypeMacro -> {
                    typeMacro.add(line)
                    if (trimmed.endsWith(";")) inTypeMacro = false
                }
                else -> gameCode.add(line)
            }
        }

        // Build wrapped code
        fullCode = if (typeMacro.isNotEmpty()) {
            typeMacro.joinToString("\n") + "\ngame main() {\n" + gameCode.joinToString("\n") + "\n}"
        } else {
            "game main() {\n" + gameCode.joinToString("\n") + "\n}"
        }
    }

    // Give ANTLR a source name that matches the URI (helps error messages)
    val chars = CharStreams.fromString(fullCode, uri.toString())
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator(uri).visitProgram(ast)
}

fun parseFile(inputFilename: String): GameAst {
    val path = Paths.get(inputFilename)
    val chars = CharStreams.fromPath(path) // source name = path.toString()
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator(path.toUri()).visitProgram(ast)
}

package vegas.frontend

import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import java.net.URI
import java.nio.file.Paths

/**
 * Vegas parse error. Thrown on the first lexer/parser error encountered;
 * the default ANTLR behaviour of printing to stderr and recovering would
 * silently accept malformed input (e.g. a stray `$ deposit` after `random`
 * would be skipped rather than reported as a syntax error).
 */
class VegasParseError(val source: String, val line: Int, val column: Int, message: String) :
    RuntimeException("$source:$line:$column: $message")

private object FailFastErrorListener : BaseErrorListener() {
    override fun syntaxError(
        recognizer: Recognizer<*, *>?,
        offendingSymbol: Any?,
        line: Int,
        charPositionInLine: Int,
        msg: String,
        e: RecognitionException?,
    ) {
        val source = recognizer?.inputStream?.sourceName ?: "<unknown>"
        throw VegasParseError(source, line, charPositionInLine + 1, msg)
    }
}

private fun buildParser(chars: CharStream): VegasParser {
    val lexer = VegasLexer(chars).apply {
        removeErrorListeners()
        addErrorListener(FailFastErrorListener)
    }
    val tokens = CommonTokenStream(lexer)
    return VegasParser(tokens).apply {
        removeErrorListeners()
        addErrorListener(FailFastErrorListener)
    }
}


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
    val ast = buildParser(chars).program()

    return AstTranslator(uri).visitProgram(ast)
}

fun parseFile(inputFilename: String): GameAst {
    val path = Paths.get(inputFilename)
    val chars = CharStreams.fromPath(path) // source name = path.toString()
    val ast = buildParser(chars).program()

    return AstTranslator(path.toUri()).visitProgram(ast)
}

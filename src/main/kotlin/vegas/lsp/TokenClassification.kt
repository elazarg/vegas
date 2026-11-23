package vegas.lsp

import org.antlr.v4.runtime.Token
import vegas.generated.VegasParser

private val operatorTexts = setOf(
    "{", "}", ",", "..", ";", "(", ")", "?", ":", "->", ".", "-", "!", "*", "/", "+",
    "!=", "==", "<", "<=", ">=", ">", "<->", "<-!->", "&&", "||", "="
)

private val keywordTexts = setOf(
    "type", "join", "yield", "reveal", "random", "withdraw", "exit",
    "where", "let", "in", "let!", "hidden", "null", "true", "false"
)


private fun classifyToken(token: Token): String? = when {
    token.type == VegasParser.ROLE_ID -> "role"
    token.type == VegasParser.LOWER_ID -> "variable"
    token.type in listOf(VegasParser.INT, VegasParser.ADDRESS, VegasParser.STRING) -> "literal"
    token.text in operatorTexts -> "operator"
    token.text in keywordTexts -> "keyword"
    else -> null
}

fun encodeToken(tokens: List<Token>, tokenTypes: List<String>): List<Int> {
    val encoded = mutableListOf<Int>()
    var lastLine = 0
    var lastChar = 0

    for (token in tokens) {
        // Skip hidden tokens (comments, whitespace, EOF)
        if (token.channel != 0 || token.type == Token.EOF) continue

        val tokenTypeName = classifyToken(token)
        val typeIndex = tokenTypes.indexOf(tokenTypeName)
        if (typeIndex == -1) continue

        val line = token.line - 1
        val char = token.charPositionInLine
        val deltaLine = line - lastLine
        val deltaChar = if (deltaLine == 0) char - lastChar else char

        encoded.addAll(listOf(deltaLine, deltaChar, token.text.length, typeIndex, 0))
        lastLine = line
        lastChar = char
    }

    return encoded
}

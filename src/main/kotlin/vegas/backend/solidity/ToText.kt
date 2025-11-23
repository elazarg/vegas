package vegas.backend.solidity

/**
 * Generate Solidity source code from AST.
 */
fun renderSolidityContract(contract: SolidityContract): String {
    return cleanupWhitespace("""
pragma solidity ^0.8.31;

${renderContract(contract)}
""".trimStart()) + "\n"
}

// ========== Contract Structure ==========

private fun renderContract(contract: SolidityContract): String {
    val parts = buildList {
        // Constructor
        add(renderConstructor(contract.constructor))

        // Enums
        contract.enums.forEach { add(renderEnum(it)) }

        // Storage
        contract.storage.forEach { add(renderStorage(it)) }

        // Modifiers
        contract.modifiers.forEach { add(renderModifier(it)) }

        // Functions
        contract.functions.forEach { add(renderFunction(it)) }

        // Events
        contract.events.forEach { add(renderEvent(it)) }

        // Fallback
        contract.fallback?.let { add(renderFallback(it)) }
    }

    val body = parts.joinToString("\n\n").prependIndent("    ")

    return """
contract ${contract.name} {
$body
}
""".trim()
}

// ========== Declarations ==========

private fun renderConstructor(constructor: Constructor): String {
    val body = constructor.body.joinToString("\n") { renderStatement(it, 1) }
    return """
constructor() {
$body
}
""".trim()
}

private fun renderEnum(enum: EnumDecl): String {
    val values = enum.values.joinToString(", ")
    return "enum ${enum.name} { $values }"
}

private fun renderStorage(decl: StorageDecl): String {
    val constModifier = if (decl.constant) " constant" else ""
    val visibility = decl.visibility.name.lowercase()
    val value = decl.value?.let { " = ${renderExpr(it)}" } ?: ""
    return "${decl.type.typeName()}$constModifier $visibility ${decl.name}$value;"
}

private fun renderModifier(modifier: ModifierDecl): String {
    val params = modifier.params.joinToString(", ") { renderParam(it) }
    val body = modifier.body.joinToString("\n") { renderStatement(it, 1) }
    return """
modifier ${modifier.name}($params) {
$body
}
""".trim()
}

private fun renderFunction(func: FunctionDecl): String {
    val params = func.params.joinToString(", ") { renderParam(it) }
    val visibility = func.visibility.name.lowercase()
    val stateMutability = when (func.stateMutability) {
        StateMutability.PURE -> " pure"
        StateMutability.VIEW -> " view"
        StateMutability.PAYABLE -> " payable"
        StateMutability.NONPAYABLE -> ""
    }
    val modifiers = if (func.modifiers.isNotEmpty()) {
        " " + func.modifiers.joinToString(" ") { renderModifierCall(it) }
    } else ""
    val returns = if (func.returns.isNotEmpty()) {
        " returns (${func.returns.joinToString(", ") { renderParam(it) }})"
    } else ""
    val body = func.body.joinToString("\n") { renderStatement(it, 1) }

    return """
function ${func.name}($params) $visibility$stateMutability$modifiers$returns {
$body
}
""".trim()
}

private fun renderParam(param: Param): String {
    return "${param.type.typeName()} ${param.name}"
}

private fun renderModifierCall(call: ModifierCall): String {
    return if (call.args.isEmpty()) {
        call.name
    } else {
        "${call.name}(${call.args.joinToString(", ") { renderExpr(it) }})"
    }
}

private fun renderEvent(event: EventDecl): String {
    val params = if (event.params.isEmpty()) {
        ""
    } else {
        event.params.joinToString(", ") { renderParam(it) }
    }
    return "event ${event.name}($params);"
}

private fun renderFallback(fallback: FallbackDecl): String {
    val visibility = fallback.visibility.name.lowercase()
    val stateMutability = when (fallback.stateMutability) {
        StateMutability.PAYABLE -> " payable"
        else -> ""
    }
    val body = fallback.body.joinToString("\n") { renderStatement(it, 1) }
    return """
receive() $visibility$stateMutability {
$body
}
""".trim()
}

// ========== Statements ==========

private fun renderStatement(stmt: Statement, indent: Int): String {
    val prefix = "    ".repeat(indent)

    return when (stmt) {
        is Statement.VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            "$prefix${stmt.type.typeName()} ${stmt.name}$init;"
        }

        is Statement.Assign -> {
            "$prefix${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)};"
        }

        is Statement.Require -> {
            prefix + "require(${renderExpr(stmt.condition)}, \"${stmt.message}\");"
        }

        is Statement.Revert -> {
            prefix + "revert(\"${stmt.message}\");"
        }

        is Statement.Emit -> {
            val args = if (stmt.args.isEmpty()) "" else stmt.args.joinToString(", ") { renderExpr(it) }
            "${prefix}emit ${stmt.event}($args);"
        }

        is Statement.If -> {
            val condition = renderExpr(stmt.condition)
            val thenBody = stmt.thenBranch.joinToString("\n") { renderStatement(it, indent + 1) }

            if (stmt.elseBranch.isEmpty()) {
                """
${prefix}if ($condition) {
$thenBody
$prefix}
                """.trim()
            } else {
                val elseBody = stmt.elseBranch.joinToString("\n") { renderStatement(it, indent + 1) }
                """
${prefix}if ($condition) {
$thenBody
$prefix} else {
$elseBody
$prefix}
                """.trim()
            }
        }

        is Statement.Block -> {
            val body = stmt.statements.joinToString("\n") { renderStatement(it, indent + 1) }
            """
$prefix{
$body
$prefix}
            """.trim()
        }

        is Statement.Return -> {
            val value = stmt.value?.let { " ${renderExpr(it)}" } ?: ""
            "${prefix}return$value;"
        }

        is Statement.ExprStmt -> {
            "$prefix${renderExpr(stmt.expr)};"
        }

        is Statement.Raw -> {
            "$prefix${stmt.code}"
        }
    }
}

// ========== Expressions ==========

private fun renderExpr(expr: SolExpr): String = when (expr) {
    // Literals
    is SolExpr.IntLit -> "${expr.value}"
    is SolExpr.BoolLit -> "${expr.value}"
    is SolExpr.StringLit -> "\"${expr.value}\""
    is SolExpr.AddressLit -> expr.hex

    // Variables and access
    is SolExpr.Var -> expr.name

    is SolExpr.Member -> "${renderExpr(expr.base)}.${expr.member}"

    is SolExpr.Index -> "${renderExpr(expr.base)}[${renderExpr(expr.index)}]"

    // Arithmetic
    is SolExpr.Add -> "(${renderExpr(expr.left)} + ${renderExpr(expr.right)})"
    is SolExpr.Sub -> "(${renderExpr(expr.left)} - ${renderExpr(expr.right)})"
    is SolExpr.Mul -> "(${renderExpr(expr.left)} * ${renderExpr(expr.right)})"
    is SolExpr.Div -> "(${renderExpr(expr.left)} / ${renderExpr(expr.right)})"
    is SolExpr.Mod -> "(${renderExpr(expr.left)} % ${renderExpr(expr.right)})"
    is SolExpr.Neg -> "(-${renderExpr(expr.operand)})"

    // Comparison
    is SolExpr.Eq -> "(${renderExpr(expr.left)} == ${renderExpr(expr.right)})"
    is SolExpr.Ne -> "(${renderExpr(expr.left)} != ${renderExpr(expr.right)})"
    is SolExpr.Lt -> "(${renderExpr(expr.left)} < ${renderExpr(expr.right)})"
    is SolExpr.Le -> "(${renderExpr(expr.left)} <= ${renderExpr(expr.right)})"
    is SolExpr.Gt -> "(${renderExpr(expr.left)} > ${renderExpr(expr.right)})"
    is SolExpr.Ge -> "(${renderExpr(expr.left)} >= ${renderExpr(expr.right)})"

    // Boolean
    is SolExpr.And -> "(${renderExpr(expr.left)} && ${renderExpr(expr.right)})"
    is SolExpr.Or -> "(${renderExpr(expr.left)} || ${renderExpr(expr.right)})"
    is SolExpr.Not -> "(!${renderExpr(expr.operand)})"

    // Ternary
    is SolExpr.Ternary -> "(${renderExpr(expr.condition)}) ? ${renderExpr(expr.ifTrue)} : ${renderExpr(expr.ifFalse)}"

    // Type operations
    is SolExpr.Cast -> "${expr.type.typeName()}(${renderExpr(expr.operand)})"

    // Function calls
    is SolExpr.Call -> {
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        "${expr.function}($args)"
    }

    is SolExpr.MemberCall -> {
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        "${renderExpr(expr.base)}.${expr.function}($args)"
    }

    is SolExpr.CallWithOptions -> {
        val options = expr.options.entries.joinToString(", ") { (k, v) ->
            "$k: ${renderExpr(v)}"
        }
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        "${renderExpr(expr.base)}.${expr.function}{$options}($args)"
    }

    // Built-ins
    is SolExpr.BuiltIn.MsgSender -> "msg.sender"
    is SolExpr.BuiltIn.MsgValue -> "msg.value"
    is SolExpr.BuiltIn.BlockTimestamp -> "block.timestamp"
    is SolExpr.BuiltIn.ThisAddress -> "address(this)"
    is SolExpr.BuiltIn.Bytes32Zero -> "bytes32(0)"

    // Solidity-specific
    is SolExpr.EnumValue -> "${expr.enumType}.${expr.value}"

    is SolExpr.AbiEncodePacked -> {
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        "abi.encodePacked($args)"
    }

    is SolExpr.Keccak256 -> "keccak256(${renderExpr(expr.data)})"

    is SolExpr.Payable -> "payable(${renderExpr(expr.address)})"
}

/**
 * Clean up excessive blank lines in generated code.
 */
fun cleanupWhitespace(code: String): String {
    return code
        .replace(Regex("( *\n){3,}"), "\n\n")  // Max 2 consecutive newlines
        .replace(Regex(" +\n"), "\n")            // Trim trailing spaces
        .trim()
}

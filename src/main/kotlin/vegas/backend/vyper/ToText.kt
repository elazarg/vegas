package vegas.backend.vyper

/**
 * Vyper AST to text rendering.
 * Handles Python-style indentation and Vyper-specific syntax.
 */

/**
 * Generate Vyper source code from AST.
 */
fun renderVyperModule(module: VyperModule): String {
    return buildString {
        appendLine("# @version ${module.version}")
        appendLine()

        // Enums
        module.enums.forEach {
            appendLine(renderEnum(it))
            appendLine()
        }

        // Constants
        module.constants.forEach {
            appendLine(renderConstant(it))
        }
        if (module.constants.isNotEmpty()) appendLine()

        // Storage
        module.storage.forEach {
            appendLine(renderStorage(it))
        }
        if (module.storage.isNotEmpty()) appendLine()

        // Constructor
        appendLine(renderConstructor(module.constructor))
        appendLine()

        // Functions
        module.functions.forEachIndexed { idx, func ->
            appendLine(renderFunction(func))
            if (idx < module.functions.size - 1) appendLine()
        }
    }.trim() + "\n"
}

private fun renderEnum(enum: EnumDecl): String {
    return buildString {
        appendLine("enum ${enum.name}:")
        enum.values.forEach { value ->
            appendLine("    $value")
        }
    }.trim()
}

private fun renderConstant(const: ConstantDecl): String {
    return "${const.name}: constant(${const.type.typeName()}) = ${renderExpr(const.value)}"
}

private fun renderStorage(storage: StorageDecl): String {
    return "${storage.name}: ${storage.type.typeName()}"
}

private fun renderConstructor(ctor: Constructor): String {
    return buildString {
        appendLine("@external")
        appendLine("def __init__():")
        if (ctor.body.isEmpty()) {
            appendLine("    pass")
        } else {
            ctor.body.forEach { stmt ->
                appendLine(renderStatement(stmt, indent = 1))
            }
        }
    }.trim()
}

private fun renderFunction(func: FunctionDecl): String {
    return buildString {
        // Decorators
        func.decorators.forEach { decorator ->
            appendLine(renderDecorator(decorator))
        }

        // Function signature
        val params = func.params.joinToString(", ") { renderParam(it) }
        appendLine("def ${func.name}($params):")

        // Body
        if (func.body.isEmpty()) {
            appendLine("    pass")
        } else {
            func.body.forEach { stmt ->
                appendLine(renderStatement(stmt, indent = 1))
            }
        }
    }.trim()
}

private fun renderDecorator(decorator: Decorator): String = when (decorator) {
    Decorator.External -> "@external"
    Decorator.Internal -> "@internal"
    Decorator.Payable -> "@payable"
    Decorator.View -> "@view"
    Decorator.Pure -> "@pure"
}

private fun renderParam(param: Param): String {
    return "${param.name}: ${param.type.typeName()}"
}

private fun renderStatement(stmt: Statement, indent: Int): String {
    val prefix = "    ".repeat(indent)

    return when (stmt) {
        is Statement.VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            "$prefix${stmt.name}: ${stmt.type.typeName()}$init"
        }

        is Statement.Assign -> {
            "$prefix${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)}"
        }

        is Statement.Assert -> {
            // Vyper assert doesn't need parentheses around the condition
            val cond = when (stmt.condition) {
                // Strip outer parentheses for assert statements
                is VyExpr.Eq, is VyExpr.Ne, is VyExpr.Lt, is VyExpr.Le, is VyExpr.Gt, is VyExpr.Ge,
                is VyExpr.And, is VyExpr.Or, is VyExpr.Not -> renderExprWithoutOuterParens(stmt.condition)
                else -> renderExpr(stmt.condition)
            }
            "$prefix" + "assert $cond, \"${stmt.message}\""
        }

        is Statement.If -> {
            buildString {
                appendLine("${prefix}if ${renderExpr(stmt.condition)}:")
                stmt.thenBranch.forEach {
                    appendLine(renderStatement(it, indent + 1))
                }
                if (stmt.elseBranch.isNotEmpty()) {
                    appendLine("${prefix}else:")
                    stmt.elseBranch.forEach {
                        appendLine(renderStatement(it, indent + 1))
                    }
                }
            }.trimEnd()
        }

        is Statement.Return -> {
            val value = stmt.value?.let { " ${renderExpr(it)}" } ?: ""
            "${prefix}return$value"
        }

        is Statement.ExprStmt -> {
            "$prefix${renderExpr(stmt.expr)}"
        }

        Statement.Pass -> {
            "${prefix}pass"
        }

        is Statement.Raw -> {
            "$prefix${stmt.code}"
        }
    }
}

/**
 * Render expression without outer parentheses for cleaner output in assertions.
 */
private fun renderExprWithoutOuterParens(expr: VyExpr): String = when (expr) {
    // Comparison - no outer parens
    is VyExpr.Eq -> "${renderExpr(expr.left)} == ${renderExpr(expr.right)}"
    is VyExpr.Ne -> "${renderExpr(expr.left)} != ${renderExpr(expr.right)}"
    is VyExpr.Lt -> "${renderExpr(expr.left)} < ${renderExpr(expr.right)}"
    is VyExpr.Le -> "${renderExpr(expr.left)} <= ${renderExpr(expr.right)}"
    is VyExpr.Gt -> "${renderExpr(expr.left)} > ${renderExpr(expr.right)}"
    is VyExpr.Ge -> "${renderExpr(expr.left)} >= ${renderExpr(expr.right)}"

    // Boolean - no outer parens
    is VyExpr.And -> "${renderExpr(expr.left)} and ${renderExpr(expr.right)}"
    is VyExpr.Or -> "${renderExpr(expr.left)} or ${renderExpr(expr.right)}"
    is VyExpr.Not -> "not ${renderExpr(expr.operand)}"

    // Everything else - use normal rendering
    else -> renderExpr(expr)
}

private fun renderExpr(expr: VyExpr): String = when (expr) {
    is VyExpr.IntLit -> "${expr.value}"
    is VyExpr.BoolLit -> if (expr.value) "True" else "False"
    is VyExpr.StringLit -> "\"${expr.value}\""
    is VyExpr.BytesLit -> "b\"${expr.value}\""

    is VyExpr.Var -> expr.name
    is VyExpr.SelfMember -> "self.${expr.member}"
    is VyExpr.Member -> "${renderExpr(expr.base)}.${expr.member}"
    is VyExpr.Index -> "${renderExpr(expr.base)}[${renderExpr(expr.index)}]"

    // Arithmetic
    is VyExpr.Add -> "(${renderExpr(expr.left)} + ${renderExpr(expr.right)})"
    is VyExpr.Sub -> "(${renderExpr(expr.left)} - ${renderExpr(expr.right)})"
    is VyExpr.Mul -> "(${renderExpr(expr.left)} * ${renderExpr(expr.right)})"
    is VyExpr.Div -> "(${renderExpr(expr.left)} / ${renderExpr(expr.right)})"
    is VyExpr.Mod -> "(${renderExpr(expr.left)} % ${renderExpr(expr.right)})"
    is VyExpr.Neg -> "(-${renderExpr(expr.operand)})"

    // Comparison
    is VyExpr.Eq -> "(${renderExpr(expr.left)} == ${renderExpr(expr.right)})"
    is VyExpr.Ne -> "(${renderExpr(expr.left)} != ${renderExpr(expr.right)})"
    is VyExpr.Lt -> "(${renderExpr(expr.left)} < ${renderExpr(expr.right)})"
    is VyExpr.Le -> "(${renderExpr(expr.left)} <= ${renderExpr(expr.right)})"
    is VyExpr.Gt -> "(${renderExpr(expr.left)} > ${renderExpr(expr.right)})"
    is VyExpr.Ge -> "(${renderExpr(expr.left)} >= ${renderExpr(expr.right)})"

    // Boolean
    is VyExpr.And -> "(${renderExpr(expr.left)} and ${renderExpr(expr.right)})"
    is VyExpr.Or -> "(${renderExpr(expr.left)} or ${renderExpr(expr.right)})"
    is VyExpr.Not -> "(not ${renderExpr(expr.operand)})"

    // Ternary
    is VyExpr.IfExpr -> "${renderExpr(expr.ifTrue)} if ${renderExpr(expr.condition)} else ${renderExpr(expr.ifFalse)}"

    // Type operations
    is VyExpr.Convert -> "convert(${renderExpr(expr.operand)}, ${expr.type.typeName()})"

    // Function calls
    is VyExpr.Call -> {
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        val kwargs = expr.kwargs.entries.joinToString(", ") { (k, v) ->
            "$k=${renderExpr(v)}"
        }
        val allArgs = listOf(args, kwargs).filter { it.isNotEmpty() }.joinToString(", ")
        "${expr.function}($allArgs)"
    }

    // Built-ins
    is VyExpr.BuiltIn.MsgSender -> "msg.sender"
    is VyExpr.BuiltIn.MsgValue -> "msg.value"
    is VyExpr.BuiltIn.BlockTimestamp -> "block.timestamp"
    is VyExpr.BuiltIn.SelfAddress -> "self"
    is VyExpr.BuiltIn.Bytes32Zero -> "empty(bytes32)"
    is VyExpr.BuiltIn.True -> "True"
    is VyExpr.BuiltIn.False -> "False"

    // Vyper-specific
    is VyExpr.EnumValue -> "${expr.enumType}.${expr.value}"

    is VyExpr.AbiEncode -> {
        val args = expr.args.joinToString(", ") { renderExpr(it) }
        "abi_encode($args, output_type=${expr.outputType.typeName()})"
    }

    is VyExpr.Keccak256 -> "keccak256(${renderExpr(expr.data)})"

    is VyExpr.RawCall -> {
        val args = buildList {
            add(renderExpr(expr.target))
            add(renderExpr(expr.data))
            expr.value?.let { add("value=${renderExpr(it)}") }
            add("max_outsize=${expr.maxOutsize}")
            expr.gas?.let { add("gas=$it") }
        }
        "raw_call(${args.joinToString(", ")})"
    }
}

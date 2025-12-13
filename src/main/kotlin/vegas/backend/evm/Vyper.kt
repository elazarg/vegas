package vegas.backend.evm

import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Render the EVM IR to Vyper source code.
 */
fun generateVyper(contract: EvmContract): String {
    return buildString {
        appendLine("# @version 0.4.0")
        appendLine()

        // Enums
        contract.enums.forEach { renderEnum(it) }
        if (contract.enums.isNotEmpty()) appendLine()

        // Events
        contract.events.forEach { renderEvent(it) }
        if (contract.events.isNotEmpty()) appendLine()

        // Storage
        // Vyper defines storage variables at the top level
        contract.storage.forEach { slot ->
            renderStorage(slot)
        }
        if (contract.storage.isNotEmpty()) appendLine()

        // Constructor
        renderConstructor(contract.initialization)
        appendLine()

        // Internal Helpers
        contract.helpers.forEach { renderFunction(it) }
        if (contract.helpers.isNotEmpty()) appendLine()

        // Game Actions
        contract.actions.forEach { renderAction(it) }

        // Fallback function (prevent accidental ETH transfers)
        renderDefaultFunction()
        appendLine()
    }
}

// =========================================================================
// Structure Rendering
// =========================================================================

private fun StringBuilder.renderEnum(e: EvmEnum) {
    appendLine("enum ${e.name}:")
    e.values.forEach {
        appendLine("    $it")
    }
}

private fun StringBuilder.renderEvent(e: EvmEvent) {
    appendLine("event ${e.name}:")
    if (e.params.isEmpty()) {
        appendLine("    pass")
    } else {
        e.params.forEach {
            appendLine("    ${it.name}: ${renderType(it.type)}")
        }
    }
}

private fun StringBuilder.renderStorage(s: EvmStorageSlot) {
    // Vyper storage: name: type
    // Constants are defined differently, but for simplicity in this backend
    // we can treat 'immutable' as public constants or just storage variables.
    // True constants in Vyper are 'NAME: constant(type) = value'
    if (s.isImmutable && s.initialValue != null) {
        appendLine("${s.name}: constant(${renderType(s.type)}) = ${renderExpr(s.initialValue)}")
    } else {
        appendLine("${s.name}: ${renderType(s.type)}")
    }
}

private fun StringBuilder.renderConstructor(init: List<EvmStmt>) {
    appendLine("@external")
    appendLine("def __init__():")
    indent {
        if (init.isEmpty()) appendLine("pass")
        else init.forEach { renderStmt(it) }
    }
}

private fun StringBuilder.renderAction(a: EvmAction) {
    // Decorators
    appendLine("@external")
    if (a.payable) appendLine("@payable")

    // Signature - parameters prefixed with underscore
    val inputs = a.inputs.joinToString(", ") { "_${it.name.name}: ${renderType(it.type)}" }
    appendLine("def ${a.name}($inputs):")

    indent {
        // Inline Checks
        a.checks.forEach { renderStmt(it) }

        // Domain guards and where clauses
        a.guards.forEach { guard ->
            renderStmt(Require(guard, "domain"))
        }

        // Render Body
        if (a.body.isEmpty() && a.checks.isEmpty() && a.guards.isEmpty() && a.updates.isEmpty()) appendLine("pass")
        else a.body.forEach { renderStmt(it) }

        // Post Updates
        a.updates.forEach { renderStmt(it) }
    }
    appendLine()
}

private fun StringBuilder.renderFunction(f: EvmFunction) {
    val inputs = f.inputs.joinToString(", ") { "${it.name.name}: ${renderType(it.type)}" }
    // Vyper visibility/decorators
    val decorator = if (f.visibility == "internal") "@internal" else "@external"
    // View/Pure? Vyper infers or uses @view/@pure.
    // EvmFunction.mutability string ("view", "pure") map to decorators.
    val mutability = if (f.mutability.isNotEmpty()) "@${f.mutability}" else ""

    appendLine(decorator)
    if (mutability.isNotEmpty()) appendLine(mutability)
    appendLine("def ${f.name}($inputs):")
    indent {
        if (f.body.isEmpty()) appendLine("pass")
        else f.body.forEach { renderStmt(it) }
    }
    appendLine()
}

// =========================================================================
// Synthesized Logic
// =========================================================================

private fun StringBuilder.renderDefaultFunction() {
    // Vyper's fallback function (prevents accidental ETH transfers)
    appendLine("@payable")
    appendLine("@external")
    appendLine("def __default__():")
    indent {
        appendLine("assert False, \"direct ETH not allowed\"")
    }
}


private fun StringBuilder.renderStmt(stmt: EvmStmt) {
    when (stmt) {
        is VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            appendLine("${stmt.name}: ${renderType(stmt.type)}$init")
        }
        is Assign -> appendLine("${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)}")
        is Return -> {
            val valStr = stmt.value?.let { " " + renderExpr(it) } ?: ""
            appendLine("return$valStr")
        }
        is Emit -> {
            // Vyper uses 'log' keyword
            val args = stmt.args.joinToString(", ") { renderExpr(it) }
            appendLine("log ${stmt.eventName}($args)")
        }
        is ExprStmt -> appendLine(renderExpr(stmt.expr))

        is Require -> appendLine("assert ${renderExpr(stmt.condition)}, \"${stmt.message}\"")

        is Revert -> {
            // Vyper `raise` doesn't take args in all versions,
            // but `assert False` is a standard way to revert with msg
            appendLine("assert False, \"${stmt.message}\"")
        }
        is If -> {
            appendLine("if ${renderExpr(stmt.condition)}:")
            indent {
                if (stmt.body.isEmpty()) appendLine("pass")
                else stmt.body.forEach { renderStmt(it) }
            }
            if (stmt.elseBody.isNotEmpty()) {
                appendLine("else:")
                indent {
                    stmt.elseBody.forEach { renderStmt(it) }
                }
            }
        }
        is Placeholder -> {} // Should not appear in Vyper logic
        is Pass -> appendLine("pass")
        is SendEth -> {
            // Store payout in local variable to avoid evaluating twice
            val payoutExpr = renderExpr(stmt.amount)
            appendLine("payout: int256 = $payoutExpr")
            appendLine("if payout > 0:")
            appendLine("    success: bool = raw_call(${renderExpr(stmt.to)}, b\"\", value=convert(payout, uint256), revert_on_failure=False)")
            appendLine("    assert success, \"ETH send failed\"")
        }
    }
}

private fun renderExpr(e: EvmExpr): String = when (e) {
    is IntLit -> e.value.toString()
    is BoolLit -> if (e.value) "True" else "False"
    is StringLit -> "\"${e.value}\""
    is BytesLit -> e.value // Assumed hex string

    is Var -> "_${e.name.name}"  // Parameters are prefixed with underscore
    is Member -> {
        if (e.base is BuiltIn.Self) "self.${e.member}"
        else "${renderExpr(e.base)}.${e.member}"
    }
    is Index -> "${renderExpr(e.base)}[${renderExpr(e.index)}]"

    is Unary -> {
        val opStr = when (e.op) {
            UnaryOp.NOT -> "not "
            UnaryOp.NEG -> "-"
        }
        "($opStr${renderExpr(e.arg)})"
    }
    is Binary -> {
        val opStr = when (e.op) {
            BinaryOp.ADD -> "+"
            BinaryOp.SUB -> "-"
            BinaryOp.MUL -> "*"
            BinaryOp.DIV -> "/"
            BinaryOp.MOD -> "%"
            BinaryOp.EQ -> "=="
            BinaryOp.NE -> "!="
            BinaryOp.LT -> "<"
            BinaryOp.LE -> "<="
            BinaryOp.GT -> ">"
            BinaryOp.GE -> ">="
            BinaryOp.AND -> "and"
            BinaryOp.OR -> "or"
        }
        "(${renderExpr(e.left)} $opStr ${renderExpr(e.right)})"
    }
    is Ternary -> "${renderExpr(e.ifTrue)} if ${renderExpr(e.cond)} else ${renderExpr(e.ifFalse)}"

    is Call -> {
        // Handle _checkReveal specially if needed, otherwise normal call
        "${e.func}(${e.args.joinToString(", ") { renderExpr(it) }})"
    }
    is MemberCall -> "${renderExpr(e.base)}.${e.func}(${e.args.joinToString(", ") { renderExpr(it) }})"

    // Built-ins
    is BuiltIn.MsgSender -> "msg.sender"
    is BuiltIn.MsgValue -> "msg.value"
    is BuiltIn.Timestamp -> "block.timestamp"
    is BuiltIn.Self -> "self"

    // Special
    is Keccak256 -> "keccak256(${renderExpr(e.data)})"

    is AbiEncode -> {
        // Vyper doesn't have abi.encodePacked.
        // We use concat(convert(arg, bytes32), ...) for basic packing
        // This is a simplification; a robust compiler would check types.
        if (e.isPacked) {
            val parts = e.args.joinToString(", ") { "convert(${it.name}, bytes32)" }
            "concat($parts)"
        } else {
            // _abi_encode intrinsic in Vyper
            "_abi_encode(${e.args.joinToString(", ") { renderExpr(it) }})"
        }
    }
    is EnumValue -> "${e.enumName}.${e.value}"
}

private fun renderType(t: EvmType): String = when (t) {
    Int256 -> "int256"
    Uint256 -> "uint256"
    Bool -> "bool"
    Address -> "address"
    Bytes32 -> "bytes32"
    is Bytes -> "Bytes[${t.maxSize}]" // Vyper requires max size
    is Mapping -> "HashMap[${renderType(t.key)}, ${renderType(t.value)}]"
    is EnumType -> t.name
}

private fun roleEnumMember(roleName: String) = "Role.$roleName"

private fun StringBuilder.indent(block: StringBuilder.() -> Unit) {
    val indented = buildString(block).trimEnd().prependIndent("    ")
    appendLine(indented)
}

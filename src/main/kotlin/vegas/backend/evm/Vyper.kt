package vegas.backend.evm

import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Renders the EVM IR directly to Vyper source code.
 */
fun generateVyper(contract: EvmContract): String {
    return buildString {
        appendLine("# @version ^0.3.7")
        appendLine()

        // 1. Enums (Vyper enum syntax)
        contract.enums.forEach { renderEnum(it) }
        if (contract.enums.isNotEmpty()) appendLine()

        // 2. Events
        contract.events.forEach { renderEvent(it) }
        if (contract.events.isNotEmpty()) appendLine()

        // 3. Storage
        // Vyper defines storage variables at the top level
        contract.storage.forEach { renderStorage(it) }
        if (contract.storage.isNotEmpty()) appendLine()

        // 4. Constructor
        renderConstructor(contract.initialization)
        appendLine()

        // 5. Game Actions
        contract.actions.forEach { renderAction(it) }

        // 6. Backend-Synthesized Functions
        renderPayoffFunction(contract.payoffs)
        appendLine()
        renderWithdrawFunction()
        appendLine()

        // 7. Internal Helpers
        if (needsCheckReveal(contract)) {
            renderCheckRevealHelper()
            appendLine()
        }
        renderMarkActionDoneHelper()
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
        appendLine("${s.name}: public(${renderType(s.type)})")
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

    // Signature
    val inputs = a.inputs.joinToString(", ") { "${it.name}: ${renderType(it.type)}" }
    appendLine("def ${a.name}($inputs):")

    indent {
        // 1. Synthesize Assertions (Replacements for Modifiers)
        // Role Check
        appendLine("assert self.roles[msg.sender] == ${roleEnumMember(a.owner)}, \"bad role\"")

        // Not Done Check
        appendLine("assert not self.actionDone[${a.actionId}], \"action already done\"")

        // Dependencies
        a.dependencies.forEach { dep ->
            appendLine("assert self.actionDone[$dep], \"dependency not met\"")
        }

        // Terminal Check
        if (a.isTerminal) {
            appendLine("assert self.actionDone[FINAL_ACTION], \"game not over\"")
            appendLine("assert not self.payoffs_distributed, \"payoffs already sent\"")
        }

        // 2. Render Body
        if (a.body.isEmpty()) appendLine("pass")
        else a.body.forEach { renderStmt(it) }
    }
    appendLine()
}

// =========================================================================
// Synthesized Logic
// =========================================================================

private fun StringBuilder.renderPayoffFunction(payoffs: Map<String, EvmExpr>) {
    appendLine("@external")
    appendLine("def distributePayoffs():")
    indent {
        appendLine("assert self.actionDone[FINAL_ACTION], \"game not over\"")
        appendLine("assert not self.payoffs_distributed, \"payoffs already sent\"")
        appendLine("self.payoffs_distributed = True")

        payoffs.forEach { (role, expr) ->
            // self.balances[self.addr_Role] = expr
            val lhs = "self.${balanceMap}[self.addr_$role]"
            val rhs = renderExpr(expr)
            appendLine("$lhs = $rhs")
        }
    }
}

private fun StringBuilder.renderWithdrawFunction() {
    appendLine("@external")
    appendLine("def withdraw():")
    indent {
        appendLine("amount: int256 = self.balances[msg.sender]")
        appendLine("assert amount > 0, \"nothing to withdraw\"")
        appendLine("self.balances[msg.sender] = 0")
        // Vyper raw_call for transfer
        appendLine("raw_call(msg.sender, b\"\", value=convert(amount, uint256))")
    }
}

private fun needsCheckReveal(c: EvmContract): Boolean {
    return c.actions.any { a ->
        a.body.any { it is ExprStmt && it.expr is Call && it.expr.func == "_checkReveal" }
    }
}

private fun StringBuilder.renderCheckRevealHelper() {
    // Helper to check commitment
    // In Vyper, we pass the parts and reconstruct hash
    appendLine("@internal")
    appendLine("@pure")
    appendLine("def _checkReveal(commitment: bytes32, packed_hash: bytes32):")
    indent {
        appendLine("assert packed_hash == commitment, \"reveal hash mismatch\"")
    }
}

private fun StringBuilder.renderMarkActionDoneHelper() {
    appendLine("@internal")
    appendLine("def _markActionDone(id: uint256):")
    indent {
        appendLine("self.actionDone[id] = True")
        appendLine("self.actionTimestamp[id] = block.timestamp")
        appendLine("self.last_timestamp = block.timestamp")
    }
}

private fun StringBuilder.renderStmt(stmt: EvmStmt) {
    when (stmt) {
        is VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            appendLine("${stmt.name}: ${renderType(stmt.type)}$init")
        }
        is Assign -> appendLine("${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)}")
        is If -> {
            appendLine("if ${renderExpr(stmt.condition)}:")
            indent { stmt.thenBody.forEach { renderStmt(it) } }
            if (stmt.elseBody.isNotEmpty()) {
                appendLine("else:")
                indent { stmt.elseBody.forEach { renderStmt(it) } }
            }
        }
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

        is Guard -> appendLine("assert ${renderExpr(stmt.condition)}, \"${stmt.message}\"")

        is Revert -> {
            // Vyper `raise` doesn't take args in all versions,
            // but `assert False` is a standard way to revert with msg
            appendLine("assert False, \"${stmt.message}\"")
        }
        is Pass -> appendLine("pass")
    }
}

private fun renderExpr(e: EvmExpr): String = when (e) {
    is IntLit -> e.value.toString()
    is BoolLit -> if (e.value) "True" else "False"
    is StringLit -> "\"${e.value}\""
    is BytesLit -> e.value // Assumed hex string

    is Var -> e.name.name
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
            "_abi_encode(${e.args.joinToString(", ") { it.name }})"
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
    val indented = buildString(block).prependIndent("    ")
    append(indented)
}
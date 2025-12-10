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
        // Add timeout infrastructure
        appendLine("TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds")
        appendLine("bailed: HashMap[Role, bool]")
        if (contract.storage.isNotEmpty()) appendLine()

        // Constructor
        renderConstructor(contract.initialization)
        appendLine()

        // Game Actions
        contract.actions.forEach { renderAction(it) }

        // Fallback function (prevent accidental ETH transfers)
        renderDefaultFunction()
        appendLine()

        // Internal Helpers
        renderCheckTimestampHelper()
        appendLine()

        if (needsCheckReveal(contract)) {
            renderCheckRevealHelper()
            appendLine()
        }
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
        // 1. Synthesize Assertions (Replacements for Modifiers)
        // Role Check (inline 'by' modifier)
        val roleCheck = "self.$roleMap[msg.sender] == ${roleEnumMember(a.invokedBy.name)}"
        appendLine("assert $roleCheck, \"bad role\"")

        // Timeout check (inline from 'by' modifier)
        appendLine("self._check_timestamp(${roleEnumMember(a.invokedBy.name)})")
        appendLine("assert not self.bailed[${roleEnumMember(a.invokedBy.name)}], \"you bailed\"")

        // Not Done Check (inline 'action' modifier)
        val actionRole = roleEnumMember(a.actionId.first.name)
        val actionIdx = a.actionId.second
        appendLine("assert not self.actionDone[$actionRole][$actionIdx], \"already done\"")

        // Dependencies (inline 'depends' modifier) - only assert is conditional on bail
        a.dependencies.forEach { dep ->
            val depRole = roleEnumMember(dep.first.name)
            val depIdx = dep.second
            appendLine("self._check_timestamp($depRole)")
            appendLine("if not self.bailed[$depRole]:")
            // Manual indentation for single assert inside if block
            appendLine("    assert self.actionDone[$depRole][$depIdx], \"dependency not satisfied\"")
        }

        // Terminal Check (inline 'at_final_phase' modifier)
        if (a.isTerminal) {
            appendLine("assert self.actionDone[FINAL_ACTION], \"game not over\"")
            appendLine("assert not self.payoffs_distributed, \"payoffs already sent\"")
        }

        // Domain guards and where clauses - always checked regardless of bail status
        a.guards.forEach { guard ->
            renderStmt(Require(guard, "domain"))
        }

        // 2. Render Body - always executed
        if (a.body.isEmpty()) appendLine("pass")
        else a.body.forEach { renderStmt(it) }

        // 3. Mark action as done (inline end of 'action' modifier)
        appendLine("self.actionDone[$actionRole][$actionIdx] = True")
        appendLine("self.actionTimestamp[$actionRole][$actionIdx] = block.timestamp")
        appendLine("self.lastTs = block.timestamp")
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

private fun StringBuilder.renderCheckTimestampHelper() {
    // Timeout handling - allows bailout if game stalls
    // Matches Solidity's _check_timestamp function
    appendLine("@internal")
    appendLine("def _check_timestamp(role: Role):")
    indent {
        appendLine("if role == Role.None:")
        indent {
            appendLine("return")
        }
        // Second condition is independent - check timeout after early return
        appendLine("if block.timestamp > self.lastTs + TIMEOUT:")
        indent {
            appendLine("self.bailed[role] = True")
            appendLine("self.lastTs = block.timestamp")
        }
    }
}

private fun needsCheckReveal(c: EvmContract): Boolean {
    return c.actions.any { a ->
        a.body.any { it is ExprStmt && it.expr is Call && it.expr.func == "_checkReveal" }
    }
}

private fun StringBuilder.renderCheckRevealHelper() {
    // Helper to check commitment-reveal scheme
    // Matches Solidity: _checkReveal(bytes32 commitment, bytes memory preimage)
    appendLine("@internal")
    appendLine("@view")
    appendLine("def _checkReveal(commitment: bytes32, preimage: Bytes[128]):")
    indent {
        appendLine("assert keccak256(preimage) == commitment, \"bad reveal\"")
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

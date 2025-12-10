package vegas.backend.evm

import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Renders the EVM IR directly to Solidity source code.
 *
 * This layer is responsible for:
 * 1. Syntax generation (braces, semicolons, types).
 * 2. Implementing the standard Vegas infrastructure (modifiers, withdraw, etc.).
 * 3. synthesizing 'distributePayoffs' from the declarative payoff map.
 */
fun generateSolidity(contract: EvmContract): String {
    return buildString {
        appendLine("pragma solidity ^0.8.31;")
        appendLine()
        appendLine("contract ${contract.name} {")

        indent {
            // 1. Enums
            contract.enums.forEach { renderEnum(it) }
            if (contract.enums.isNotEmpty()) appendLine()

            // 2. Events
            contract.events.forEach { renderEvent(it) }
            if (contract.events.isNotEmpty()) appendLine()

            // 3. Storage
            contract.storage.forEach { renderStorage(it) }
            if (contract.storage.isNotEmpty()) appendLine()

            // 4. Standard Modifiers
            renderInfrastructureModifiers()
            appendLine()

            // 5. Constructor
            renderConstructor(contract.initialization)
            appendLine()

            // 6. Game Actions
            contract.actions.forEach { renderAction(it) }

            // 7. Backend-Synthesized Functions
            renderPayoffFunction(contract.payoffs)
            appendLine()
            renderWithdrawFunction()
            appendLine()

            // 8. Internal Helpers (e.g. Commit/Reveal utils)
            // We check if we need them based on whether they are used?
            // Or just emit them if the game has commit/reveal logic.
            // For simplicity, we emit the standard helper if needed.
//            if (needsCheckReveal(contract)) {
//                appendLine()
//            }
        }

        appendLine("}")
    }
}

// =========================================================================
// Structure Rendering
// =========================================================================

private fun StringBuilder.renderEnum(e: EvmEnum) {
    appendLine("enum ${e.name} { ${e.values.joinToString(", ")} }")
}

private fun StringBuilder.renderEvent(e: EvmEvent) {
    val params = e.params.joinToString(", ") { "${renderType(it.type)} ${it.name}" }
    appendLine("event ${e.name}($params);")
}

private fun StringBuilder.renderStorage(s: EvmStorageSlot) {
    val typeStr = renderType(s.type)
    val constant = if (s.isImmutable) " constant" else ""
    val init = s.initialValue?.let { " = ${renderExpr(it)}" } ?: ""
    appendLine("$typeStr$constant public ${s.name}$init;")
}

private fun StringBuilder.renderInfrastructureModifiers() {
    appendLine("""
        receive() public payable {
            revert("direct ETH not allowed");
        }
        modifier depends(uint256 actionId) {
            require(actionDone[actionId], "dependency not satisfied");
        }
        modifier notDone(uint256 actionId) {
            require((!actionDone[actionId]), "already done");
        }
        modifier by(Role r) {
            require((${roleMap}[msg.sender] == r), "bad role");
        }
        modifier at_final_phase() {
            require(actionDone[FINAL_ACTION], "game not over");
            require((!payoffs_distributed), "payoffs already sent");
        }
        function _checkReveal(bytes32 commitment, bytes preimage) internal pure {
            require((keccak256(preimage) == commitment), "bad reveal");
        }
        function _markActionDone(uint256 actionId) internal {
            actionDone[actionId] = true;
            actionTimestamp[actionId] = block.timestamp;
            lastTs = block.timestamp;
        }
    """.trimIndent())
}

private fun StringBuilder.renderConstructor(init: List<EvmStmt>) {
    appendLine("constructor() {")
    indent {
        init.forEach { renderStmt(it) }
    }
    appendLine("}")
}

private fun StringBuilder.renderAction(a: EvmAction) {
    val inputs = a.inputs.joinToString(", ") { "${renderType(it.type)} ${it.name}" }
    val visibility = "public" // Actions are always public entry points
    val mutability = if (a.payable) " payable" else ""

    // Synthesize Modifiers from Declarative Constraints
    val modifiers = buildList {
        add("by(${roleEnumName}.${a.owner})")
        add("notDone(${a.actionId})")
        a.dependencies.forEach { dep -> add("depends($dep)") }
        if (a.isTerminal) add("at_final_phase") // Rare, usually payoffs are separate
    }.joinToString(" ")

    appendLine("function ${a.name}($inputs) $visibility$mutability $modifiers {")
    indent {
        a.body.forEach { renderStmt(it) }
    }
    appendLine("}")
    appendLine()
}

// =========================================================================
// Synthesized Logic
// =========================================================================

private fun StringBuilder.renderPayoffFunction(payoffs: Map<String, EvmExpr>) {
    appendLine("function distributePayoffs() public at_final_phase {")
    indent {
        appendLine("payoffs_distributed = true;")
        payoffs.forEach { (role, expr) ->
            // balances[address_Role] = expr
            // We construct the assignment statement manually here or render string directly
            val lhs = "${balanceMap}[${roleAddr(role)}]"
            val rhs = renderExpr(expr)
            appendLine("$lhs = $rhs;")
        }
    }
    appendLine("}")
}

private fun StringBuilder.renderWithdrawFunction() {
    appendLine("""
        function withdraw() public {
            int256 bal = ${balanceMap}[msg.sender];
            require((bal > 0), "no funds");
            ${balanceMap}[msg.sender] = 0;
            (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
            require(ok, "ETH send failed");
        }
    """.trimIndent())
}

private fun needsCheckReveal(c: EvmContract): Boolean {
    // Simple heuristic: if any action body calls "_checkReveal"
    return c.actions.any { a ->
        a.body.any { it is ExprStmt && it.expr is Call && it.expr.func == "_checkReveal" }
    }
}

private fun StringBuilder.renderStmt(stmt: EvmStmt) {
    when (stmt) {
        is VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            appendLine("${renderType(stmt.type)} ${stmt.name}$init;")
        }
        is Assign -> appendLine("${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)};")
        is If -> {
            appendLine("if (${renderExpr(stmt.condition)}) {")
            indent { stmt.thenBody.forEach { renderStmt(it) } }
            if (stmt.elseBody.isNotEmpty()) {
                appendLine("} else {")
                indent { stmt.elseBody.forEach { renderStmt(it) } }
                appendLine("}")
            } else {
                appendLine("}")
            }
        }
        is Return -> {
            val valStr = stmt.value?.let { " " + renderExpr(it) } ?: ""
            appendLine("return$valStr;")
        }
        is Emit -> {
            val args = stmt.args.joinToString(", ") { renderExpr(it) }
            appendLine("emit ${stmt.eventName}($args);")
        }
        is ExprStmt -> appendLine("${renderExpr(stmt.expr)};")
        is Guard -> appendLine("require(${renderExpr(stmt.condition)}, \"${stmt.message}\");")
        is Revert -> appendLine("revert(\"${stmt.message}\");")
        is Pass -> {} // No-op in Solidity
    }
}

private fun renderExpr(e: EvmExpr): String = when (e) {
    is IntLit -> e.value.toString()
    is BoolLit -> e.value.toString()
    is StringLit -> "\"${e.value}\""
    is BytesLit -> e.value // Assumed to be hex string like "0x1234"

    is Var -> e.name.name
    is Member -> {
        if (e.base is BuiltIn.Self) e.member // "self.x" -> "x" in Solidity
        else "${renderExpr(e.base)}.${e.member}"
    }
    is Index -> "${renderExpr(e.base)}[${renderExpr(e.index)}]"

    is Unary -> {
        val opStr = when (e.op) {
            UnaryOp.NOT -> "!"
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
            BinaryOp.AND -> "&&"
            BinaryOp.OR -> "||"
        }
        "(${renderExpr(e.left)} $opStr ${renderExpr(e.right)})"
    }
    is Ternary -> "(${renderExpr(e.cond)} ? ${renderExpr(e.ifTrue)} : ${renderExpr(e.ifFalse)})"

    is Call -> "${e.func}(${e.args.joinToString(", ") { renderExpr(it) }})"
    is MemberCall -> "${renderExpr(e.base)}.${e.func}(${e.args.joinToString(", ") { renderExpr(it) }})"

    // Built-ins
    is BuiltIn.MsgSender -> "msg.sender"
    is BuiltIn.MsgValue -> "msg.value"
    is BuiltIn.Timestamp -> "block.timestamp"
    is BuiltIn.Self -> "address(this)"

    // Special
    is Keccak256 -> "keccak256(${renderExpr(e.data)})"
    is AbiEncode -> {
        val args = e.args.joinToString(", ") { it.name }
        if (e.isPacked) "abi.encodePacked($args)" else "abi.encode($args)"
    }
    is EnumValue -> "${e.enumName}.${e.value}"
}

private fun renderType(t: EvmType): String = when (t) {
    Int256 -> "int256"
    Uint256 -> "uint256"
    Bool -> "bool"
    Address -> "address"
    Bytes32 -> "bytes32"
    is Bytes -> "bytes" // Solidity dynamic bytes
    is Mapping -> "mapping(${renderType(t.key)} => ${renderType(t.value)})"
    is EnumType -> t.name
}

private fun StringBuilder.indent(block: StringBuilder.() -> Unit) {
    val indented = buildString(block).prependIndent("    ")
    append(indented)
}

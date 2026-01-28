package vegas.backend.evm

import vegas.backend.evm.EvmConstants.TIMEOUT_SECONDS
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
        append("contract ${contract.name}")

        block {
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
        }
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
        receive() external payable {
            revert("direct ETH not allowed");
        }

        uint256 constant public TIMEOUT = $TIMEOUT_SECONDS;

        mapping(Role => bool) private bailed;

        function _check_timestamp(Role role) private {
            if (role == Role.None) {
                return;
            }
            if (block.timestamp > lastTs + TIMEOUT) {
                bailed[role] = true;
                lastTs = block.timestamp;
            }
        }

        modifier depends(Role role, uint256 actionId) {
            _check_timestamp(role);
            if (!bailed[role]) {
                require(actionDone[role][actionId], "dependency not satisfied");
            }
            _;
        }

        modifier action(Role role, uint256 actionId) {
            require((!actionDone[role][actionId]), "already done");
            actionDone[role][actionId] = true;
            _;
            actionTimestamp[role][actionId] = block.timestamp;
            lastTs = block.timestamp;
        }

        modifier by(Role role) {
            require((${roleMap}[msg.sender] == role), "bad role");
            _check_timestamp(role);
            require(!bailed[role], "you bailed");
            _;
        }

        bytes32 private constant COMMIT_TAG = keccak256("VEGAS_COMMIT_V1");
        
        function _commitmentHash(Role role, address actor, bytes memory payload) internal view returns (bytes32) {
            return keccak256(abi.encode(
                COMMIT_TAG,
                address(this),
                role,
                actor,
                keccak256(payload)
            ));
        }
        
        function _checkReveal(bytes32 commitment, Role role, address actor, bytes memory payload) internal view {
            require(_commitmentHash(role, actor, payload) == commitment, "bad reveal");
        }

    """.trimIndent())
}

private fun StringBuilder.renderConstructor(init: List<EvmStmt>) {
    append("constructor()")
    block {
        init.forEach { renderStmt(it) }
    }
}

private fun StringBuilder.renderAction(a: EvmAction) {
    val inputs = a.inputs.joinToString(", ") { "${renderType(it.type)} ${renderExpr(Var(it.name))}" }
    val visibility = "public" // Actions are always public entry points
    val mutability = if (a.payable) " payable" else ""

    // Synthesize Modifiers from Declarative Constraints
    val modifiers = buildList {
        add("by(${roleEnumName}.${a.invokedBy})")
        add("action(Role.${a.actionId.first}, ${a.actionId.second})")
        a.dependencies.forEach { dep -> add("depends(Role.${dep.first}, ${dep.second})") }
    }.joinToString(" ")

    append("function ${a.name}($inputs) $visibility$mutability $modifiers")
    block {
        a.guards.forEach { guard ->
            renderStmt(Require(guard, "domain"))
        }
        a.body.forEach { renderStmt(it) }
    }
    appendLine()
}

// =========================================================================
// Synthesized Logic
// =========================================================================

private fun StringBuilder.renderStmt(stmt: EvmStmt) {
    when (stmt) {
        is VarDecl -> {
            val init = stmt.init?.let { " = ${renderExpr(it)}" } ?: ""
            appendLine("${renderType(stmt.type)} ${stmt.name}$init;")
        }
        is Assign -> appendLine("${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)};")
        is Return -> {
            val valStr = stmt.value?.let { " " + renderExpr(it) } ?: ""
            appendLine("return$valStr;")
        }
        is Emit -> {
            val args = stmt.args.joinToString(", ") { renderExpr(it) }
            appendLine("emit ${stmt.eventName}($args);")
        }
        is ExprStmt -> appendLine("${renderExpr(stmt.expr)};")
        is Require -> appendLine("require(${renderExpr(stmt.condition)}, \"${stmt.message}\");")
        is Revert -> appendLine("revert(\"${stmt.message}\");")
        is Pass -> {} // No-op in Solidity
        is SendEth -> {
            // Only send if positive.
            // Use renderPayoffExpr to ensure int256 type for nested ternaries.
            appendLine("int256 payout = ${renderPayoffExpr(stmt.amount)};")
            appendLine("if (payout > 0) {")
            appendLine("    (bool ok, ) = payable(${renderExpr(stmt.to)}).call{value: uint256(payout)}(\"\");")
            appendLine("    require(ok, \"ETH send failed\");")
            appendLine("}")
        }
        is CheckReveal -> {
            // Verify commitment with role/actor binding to prevent mirroring attacks
            // Actor is always msg.sender (enforced by type system)
            val payload = stmt.payload.joinToString(", ") { renderExpr(it) }
            appendLine("_checkReveal(${renderExpr(stmt.commitment)}, $roleEnumName.${stmt.role.name}, msg.sender, abi.encode($payload));")
        }
    }
}

/**
 * Render an expression in a payoff (int256) context.
 * Integer literals are wrapped in int256() to avoid Solidity's
 * implicit narrowing in ternary expressions (bool ? 0 : 100 → uint8).
 */
private fun renderPayoffExpr(e: EvmExpr): String = when (e) {
    is IntLit -> "int256(${e.value})"
    is Ternary -> "(${renderPayoffExpr(e.cond)} ? ${renderPayoffExpr(e.ifTrue)} : ${renderPayoffExpr(e.ifFalse)})"
    is Binary -> "(${renderPayoffExpr(e.left)} ${when (e.op) {
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
    }} ${renderPayoffExpr(e.right)})"
    is Unary -> "(${when (e.op) {
        UnaryOp.NOT -> "!"
        UnaryOp.NEG -> "-"
    }}${renderPayoffExpr(e.arg)})"
    // For all other node types, delegate to renderExpr
    else -> renderExpr(e)
}

private fun renderExpr(e: EvmExpr): String = when (e) {
    is IntLit -> e.value.toString()
    is BoolLit -> e.value.toString()
    is StringLit -> "\"${e.value}\""
    is BytesLit -> e.value // Assumed to be hex string like "0x1234"

    is Var -> "_${e.name.name}"
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
        val args = e.args.joinToString(", ") { renderExpr(it) }
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

private fun StringBuilder.block(block: StringBuilder.() -> Unit) {
    appendLine(" {")
    val indented = buildString(block).prependIndent("    ").trimEnd()
    appendLine(indented)
    appendLine("}")
}

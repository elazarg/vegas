package vegas.backend.evm

import vegas.backend.evm.EvmConstants.TIMEOUT_SECONDS
import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Render the EVM IR to Vyper source code, implementing the same
 * [EvmSchedule] semantics as the Solidity backend.
 */
fun generateVyper(contract: EvmContract): String {
    require(contract.audit == null) {
        "Terminal audit is implemented for the Solidity backend only; compile without an audit policy for Vyper"
    }
    val schedule = contract.schedule
    return buildString {
        appendLine("#pragma version ^0.4.3")
        appendLine()

        if (schedule.usesBeacon) {
            appendLine("# A public randomness beacon. randomnessAfter(t) returns the output of the")
            appendLine("# first round scheduled strictly after t, with that round's time, or zero")
            appendLine("# while the round is not yet published.")
            appendLine("interface IVegasBeacon:")
            appendLine("    def randomnessAfter(timestamp: uint256) -> (bytes32, uint256): view")
            appendLine()
        }

        // Enums
        contract.enums.forEach { renderEnum(it) }
        if (contract.enums.isNotEmpty()) appendLine()

        // Events
        contract.events.forEach { renderEvent(it) }
        if (contract.events.isNotEmpty()) appendLine()

        // Storage
        contract.storage.forEach { slot ->
            renderStorage(slot)
        }
        appendLine("TIMEOUT: public(constant(uint256)) = $TIMEOUT_SECONDS")
        appendLine("NODE_COUNT: public(constant(uint256)) = ${schedule.nodes.size}")
        appendLine("deployedAt: public(immutable(uint256))")
        if (schedule.usesBeacon) appendLine("BEACON: public(immutable(IVegasBeacon))")
        appendLine("COMMIT_TAG: immutable(bytes32)")
        appendLine("# Readiness time of each node: when its last predecessor resolved (0 = not ready).")
        appendLine("readyAt: public(HashMap[uint256, uint256])")
        appendLine("# Resolution time of each node: when it was played, or resolved without a value (0 = unresolved).")
        appendLine("resolvedAt: public(HashMap[uint256, uint256])")
        appendLine("# When a role quit: the deadline it missed (0 = active). Quitting is persistent.")
        appendLine("quitAt: public(HashMap[Role, uint256])")
        appendLine("# Set when a role failed to join: play never starts and deposits are refunded.")
        appendLine("aborted: public(bool)")
        appendLine("# Every node below this position is resolved.")
        appendLine("settledPrefix: public(uint256)")
        appendLine()

        // Constructor
        renderConstructor(schedule, contract.initialization)
        appendLine()

        renderSchedule(schedule)

        // Game Actions
        contract.actions.forEach { renderAction(it) }

        // Withdrawals
        contract.withdrawals.forEach { renderWithdrawal(it) }

        // Fallback function (prevent accidental ETH transfers)
        renderDefaultFunction()
        appendLine()

        // Internal Helpers
        if (needsCheckReveal(contract)) {
            renderCheckRevealHelper()
            appendLine()
        }
    }
}

// =========================================================================
// Structure Rendering
// =========================================================================

/**
 * Vyper flags start at 1 and the zero value is `empty(Role)`, which is what
 * an unassigned address maps to; the IR's `None` member is rendered as that.
 */
private fun StringBuilder.renderEnum(e: EvmEnum) {
    appendLine("flag ${e.name}:")
    e.values.filter { it != roleNone }.forEach {
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
    if (s.isImmutable && s.initialValue != null) {
        appendLine("${s.name}: public(constant(${renderType(s.type)})) = ${renderExpr(s.initialValue)}")
    } else {
        appendLine("${s.name}: public(${renderType(s.type)})")
    }
}

private fun StringBuilder.renderConstructor(schedule: EvmSchedule, init: List<EvmStmt>) {
    appendLine("@deploy")
    appendLine(if (schedule.usesBeacon) "def __init__(beacon: IVegasBeacon):" else "def __init__():")
    indent {
        appendLine("deployedAt = block.timestamp")
        if (schedule.usesBeacon) appendLine("BEACON = beacon")
        appendLine("COMMIT_TAG = keccak256(\"VEGAS_COMMIT_V1\")")
        init.forEach { renderStmt(it) }
    }
}

private fun StringBuilder.renderSchedule(schedule: EvmSchedule) {
    val nodes = schedule.nodes
    renderPureTable("_owner", "Role", nodes.map { roleEnumMember(it.owner.name) })
    renderPureTable("_predecessors", "uint256", nodes.map { it.predecessorMask.toString() })
    renderPureTable("_isJoin", "bool", nodes.map { if (it.kind == EvmNodeKind.JOIN) "True" else "False" })
    if (schedule.usesBeacon) {
        renderPureTable("_isDraw", "bool", nodes.map { if (it.kind == EvmNodeKind.DRAW) "True" else "False" })
    }

    appendLine("""
        # Resolve every node that can be resolved now. Anyone may call this.
        @external
        def settle():
            self._settle()

        @internal
        def _settle():
            start: uint256 = self.settledPrefix
            prefix: uint256 = start
            contiguous: bool = True
            for i: uint256 in range(start, NODE_COUNT, bound=NODE_COUNT):
                if self.resolvedAt[i] == 0:
                    self._resolve(i)
                if contiguous and self.resolvedAt[i] != 0:
                    prefix = i + 1
                else:
                    contiguous = False
            self.settledPrefix = prefix

        @internal
        @view
        def _readiness(i: uint256) -> uint256:
            ready: uint256 = deployedAt
            predecessors: uint256 = self._predecessors(i)
            for j: uint256 in range(NODE_COUNT):
                if j >= i:
                    break
                if (predecessors >> j) & 1 == 1:
                    t: uint256 = self.resolvedAt[j]
                    if t == 0:
                        return 0
                    if t > ready:
                        ready = t
            return ready

        @internal
        def _resolve(i: uint256):
            ready: uint256 = self.readyAt[i]
            if ready == 0:
                ready = self._readiness(i)
                if ready == 0:
                    return
                self.readyAt[i] = ready
            if self.aborted:
                self.resolvedAt[i] = ready
                return
    """.trimIndent())
    if (schedule.usesBeacon) {
        appendLine("""
            |    if self._isDraw(i):
            |        value: bytes32 = empty(bytes32)
            |        roundTime: uint256 = 0
            |        value, roundTime = staticcall BEACON.randomnessAfter(ready)
            |        if value != empty(bytes32):
            |            # A resolution time is never in the future, whatever the beacon reports.
            |            self._draw(i, value)
            |            self.resolvedAt[i] = max(min(roundTime, block.timestamp), ready)
            |        return
        """.trimMargin())
    }
    appendLine("""
        |    owner: Role = self._owner(i)
        |    quit: uint256 = self.quitAt[owner]
        |    if quit != 0:
        |        self.resolvedAt[i] = max(quit, ready)
        |        return
        |    if block.timestamp > ready + TIMEOUT:
        |        self.quitAt[owner] = ready + TIMEOUT
        |        self.resolvedAt[i] = ready + TIMEOUT
        |        if self._isJoin(i):
        |            self.aborted = True
        |
        |# Settle, then require that node i is ready, unresolved, and owned by the caller's role.
        |@internal
        |def _beginMove(i: uint256, role: Role):
        |    self._settle()
        |    assert self.roles[msg.sender] == role, "bad role"
        |    assert self.readyAt[i] != 0, "not ready"
        |    assert self.resolvedAt[i] == 0, "not open"
        |
        |@internal
        |def _endMove(i: uint256):
        |    self.resolvedAt[i] = block.timestamp
    """.trimMargin())
    appendLine()

    if (schedule.usesBeacon) {
        appendLine("@internal")
        appendLine("def _draw(i: uint256, _${BEACON_VALUE.name}: bytes32):")
        indent {
            schedule.draws.forEachIndexed { k, draw ->
                appendLine("${if (k == 0) "if" else "elif"} i == ${draw.node}:")
                indent { draw.body.forEach { renderStmt(it) } }
            }
        }
        appendLine()
    }
}

/**
 * A constant lookup `name(i)` over schedule positions, as an if-chain.
 * Declared `@view`: Vyper does not allow flag members in `@pure` functions.
 */
private fun StringBuilder.renderPureTable(name: String, type: String, values: List<String>) {
    appendLine("@internal")
    appendLine("@view")
    appendLine("def $name(i: uint256) -> $type:")
    indent {
        values.dropLast(1).forEachIndexed { i, v ->
            appendLine("if i == $i:")
            appendLine("    return $v")
        }
        appendLine("return ${values.last()}")
    }
    appendLine()
}

private fun StringBuilder.renderAction(a: EvmAction) {
    // Decorators
    appendLine("@external")
    if (a.payable) appendLine("@payable")

    // Signature - parameters prefixed with underscore
    val inputs = a.inputs.joinToString(", ") { "_${it.name.name}: ${renderType(it.type)}" }
    appendLine("def ${a.name}($inputs):")

    indent {
        appendLine("self._beginMove(${a.node}, ${roleEnumMember(a.invokedBy.name)})")
        a.guards.forEach { guard ->
            renderStmt(Require(guard, "domain"))
        }
        a.body.forEach { renderStmt(it) }
        appendLine("self._endMove(${a.node})")
    }
    appendLine()
}

private fun StringBuilder.renderWithdrawal(w: EvmWithdrawal) {
    val role = w.role.name
    appendLine("@external")
    appendLine("def ${w.name}():")
    indent {
        appendLine("self._settle()")
        appendLine("assert self.$roleMap[msg.sender] == ${roleEnumMember(role)}, \"bad role\"")
        appendLine("assert not self.claimed_$role, \"already claimed\"")
        appendLine("payout: int256 = 0")
        appendLine("if self.aborted:")
        appendLine("    payout = ${w.refund} if self.${roleJoined(role)} else 0")
        appendLine("else:")
        appendLine("    assert self.settledPrefix == NODE_COUNT, \"game not finished\"")
        appendLine("    payout = ${renderExpr(w.payout)}")
        appendLine("self.claimed_$role = True")
        appendLine("if payout > 0:")
        appendLine("    success: bool = raw_call(self.${roleAddr(role)}, b\"\", value=convert(payout, uint256), revert_on_failure=False)")
        appendLine("    assert success, \"ETH send failed\"")
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

private fun needsCheckReveal(c: EvmContract): Boolean {
    return c.actions.any { a ->
        a.body.any { it is CheckReveal }
    }
}

private fun StringBuilder.renderCheckRevealHelper() {
    // Helper to check commitment-reveal scheme with role/actor binding
    // Binds commitment to (COMMIT_TAG, contract instance, role, actor, payload hash)
    // This prevents mirroring attacks where one player reuses another's commitment
    appendLine("@internal")
    appendLine("@view")
    appendLine("def _checkReveal(commitment: bytes32, role: Role, actor: address, payload: Bytes[256]):")
    indent {
        appendLine("expected: bytes32 = keccak256(abi_encode(COMMIT_TAG, self, role, actor, keccak256(payload)))")
        appendLine("assert expected == commitment, \"bad reveal\"")
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
        is CheckReveal -> {
            // Verify commitment with role/actor binding to prevent copy-commit attacks
            // Actor is always msg.sender (enforced by type system)
            val payload = stmt.payload.joinToString(", ") { renderExpr(it) }
            appendLine("self._checkReveal(${renderExpr(stmt.commitment)}, Role.${stmt.role.name}, msg.sender, abi_encode($payload))")
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
            BinaryOp.DIV -> "//"
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
    // Parenthesized: a bare Vyper conditional expression binds looser than
    // arithmetic and comparisons, so `x + a if c else b` means `(x + a) if c else b`.
    is Ternary -> "(${renderExpr(e.ifTrue)} if ${renderExpr(e.cond)} else ${renderExpr(e.ifFalse)})"

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
            "abi_encode(${e.args.joinToString(", ") { renderExpr(it) }})"
        }
    }
    is AbiEncodeRaw -> "abi_encode(${e.args.joinToString(", ") { renderExpr(it) }})"
    is EnumValue -> if (e.value == roleNone) "empty(${e.enumName})" else "${e.enumName}.${e.value}"
    is Cast -> "convert(${renderExpr(e.arg)}, ${renderType(e.type)})"
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

private fun roleEnumMember(roleName: String) =
    if (roleName == roleNone) "empty($roleEnumName)" else "$roleEnumName.$roleName"

private fun StringBuilder.indent(block: StringBuilder.() -> Unit) {
    val indented = buildString(block).trimEnd().prependIndent("    ")
    appendLine(indented)
}

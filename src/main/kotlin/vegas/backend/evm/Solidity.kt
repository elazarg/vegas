package vegas.backend.evm

import vegas.backend.evm.EvmConstants.BEACON_DELAY_SECONDS
import vegas.backend.evm.EvmConstants.TIMEOUT_SECONDS
import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

/**
 * Renders the EVM IR directly to Solidity source code.
 *
 * This layer is responsible for:
 * 1. Syntax generation (braces, semicolons, types).
 * 2. Implementing the [EvmSchedule]: readiness, deadlines, quitting and aborts.
 * 3. Rendering the per-role withdrawals.
 */
fun generateSolidity(contract: EvmContract): String {
    return buildString {
        appendLine("// SPDX-License-Identifier: MIT")
        appendLine("pragma solidity ^0.8.37;")
        appendLine()
        if (contract.schedule.usesBeacon) {
            renderBeaconInterface()
            appendLine()
        }
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

            // 4. Schedule and commitment infrastructure
            renderInfrastructure(contract.schedule, contract.audit)
            appendLine()

            // 5. Terminal audit
            if (contract.audit != null) {
                renderAudit(contract, contract.audit)
                appendLine()
            }

            // 6. Constructor
            renderConstructor(contract.schedule, contract.initialization, contract.audit)
            appendLine()

            // 7. Game Actions
            contract.actions.forEach { renderAction(it, contract.audit) }

            // 8. Withdrawals
            contract.withdrawals.forEach { renderWithdrawal(it, contract.audit) }
        }
    }
}

// =========================================================================
// Structure Rendering
// =========================================================================

private fun StringBuilder.renderBeaconInterface() {
    appendLine("""
        /// A public randomness beacon. `randomnessAfter(t)` returns the output of
        /// the first round scheduled strictly after `t`, with that round's time,
        /// or zero while the round is not yet published.
        interface IVegasBeacon {
            function randomnessAfter(uint256 timestamp) external view returns (bytes32 value, uint256 roundTime);
        }
    """.trimIndent())
}

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

private fun StringBuilder.renderInfrastructure(schedule: EvmSchedule, audit: EvmAudit?) {
    val nodes = schedule.nodes
    appendLine("""
        receive() external payable {
            revert("direct ETH not allowed");
        }

        uint256 constant public TIMEOUT = $TIMEOUT_SECONDS;
        uint256 constant public NODE_COUNT = ${nodes.size};
        uint256 public immutable deployedAt;
    """.trimIndent())
    if (schedule.usesBeacon) {
        appendLine("IVegasBeacon public immutable BEACON;")
        appendLine("/// A draw takes the first beacon round after its readiness plus this delay,")
        appendLine("/// by which time the block that made it ready is final.")
        appendLine("uint256 constant public BEACON_DELAY = $BEACON_DELAY_SECONDS;")
    }
    appendLine("""

        /// Readiness time of each node: when its last predecessor resolved (0 = not ready).
        mapping(uint256 => uint256) public readyAt;
        /// Resolution time of each node: when it was played, or resolved without a value (0 = unresolved).
        mapping(uint256 => uint256) public resolvedAt;
        /// When a role quit: the deadline it missed (0 = active). Quitting is persistent.
        mapping(Role => uint256) public quitAt;
        /// Set when a role failed to join: play never starts and deposits are refunded.
        bool public aborted;
        /// Every node below this position is resolved.
        uint256 public settledPrefix;
    """.trimIndent())
    appendLine()

    renderPureTable("_owner", "Role", nodes.map { "Role.${it.owner.name}" })
    renderPureTable("_predecessors", "uint256", nodes.map { it.predecessorMask.toString() })
    renderPureTable("_isJoin", "bool", nodes.map { (it.kind == EvmNodeKind.JOIN).toString() })
    if (schedule.usesBeacon) {
        renderPureTable("_isDraw", "bool", nodes.map { (it.kind == EvmNodeKind.DRAW).toString() })
    }

    appendLine("""
        /// Resolve every node that can be resolved now. Anyone may call this.
        function settle() public {
            _settle();
        }

        function _settle() internal {
            uint256 prefix = settledPrefix;
            bool contiguous = true;
            for (uint256 i = prefix; i < NODE_COUNT; i++) {
                if (resolvedAt[i] == 0) _resolve(i);@@SETTLE_ANCHOR@@
                if (contiguous && resolvedAt[i] != 0) {
                    prefix = i + 1;
                } else {
                    contiguous = false;
                }
            }
            settledPrefix = prefix;@@SETTLE_END@@
        }

        function _readiness(uint256 i) internal view returns (uint256) {
            uint256 ready = deployedAt;
            uint256 predecessors = _predecessors(i);
            for (uint256 j = 0; j < i; j++) {
                if ((predecessors >> j) & 1 == 1) {
                    uint256 t = resolvedAt[j];
                    if (t == 0) return 0;
                    if (t > ready) ready = t;
                }
            }
            return ready;
        }

        function _resolve(uint256 i) internal {
            uint256 ready = readyAt[i];
            if (ready == 0) {
                ready = _readiness(i);
                if (ready == 0) return;
                readyAt[i] = ready;@@READY_BLOCK@@
            }
            if (aborted) {
                resolvedAt[i] = ready;
                return;
            }
    """.trimIndent().withAudit(audit))
    if (schedule.usesBeacon) {
        appendLine("""
            |    if (_isDraw(i)) {
            |        (bytes32 value, uint256 roundTime) = BEACON.randomnessAfter(ready + BEACON_DELAY);
            |        if (value != bytes32(0)) {
            |            // A resolution time is never in the future, whatever the beacon reports.
            |            if (roundTime > block.timestamp) roundTime = block.timestamp;
            |            _draw(i, value);
            |            resolvedAt[i] = roundTime > ready ? roundTime : ready;
            |        }
            |        return;
            |    }
        """.trimMargin())
    }
    appendLine("""
        |    Role owner = _owner(i);
        |    uint256 quit = quitAt[owner];
        |    if (quit != 0) {
        |        resolvedAt[i] = quit > ready ? quit : ready;
        |        return;
        |    }
        |    if (block.timestamp > ready + TIMEOUT) {
        |        quitAt[owner] = ready + TIMEOUT;@@MISSED_BINDING@@
        |        resolvedAt[i] = ready + TIMEOUT;
        |        if (_isJoin(i)) aborted = true;
        |    }
        |}
        |
        |/// Settle, then require that node `i` is ready, unresolved, and owned by the caller's role.
        |function _beginMove(uint256 i, Role role) internal {
        |    _settle();
        |    require(roles[msg.sender] == role, "bad role");
        |    require(readyAt[i] != 0, "not ready");
        |    require(resolvedAt[i] == 0, "not open");
        |}
        |
        |function _endMove(uint256 i) internal {
        |    resolvedAt[i] = block.timestamp;@@END_MOVE@@
        |}
        |
        |bytes32 private constant COMMIT_TAG = keccak256("VEGAS_COMMIT_V1");
        |
        |function _commitmentHash(Role role, address actor, bytes memory payload) internal view returns (bytes32) {
        |    return keccak256(abi.encode(
        |        COMMIT_TAG,
        |        address(this),
        |        role,
        |        actor,
        |        keccak256(payload)
        |    ));
        |}
        |
        |function _checkReveal(bytes32 commitment, Role role, address actor, bytes memory payload) internal view {
        |    require(_commitmentHash(role, actor, payload) == commitment, "bad reveal");
        |}
    """.trimMargin().withAudit(audit))

    if (schedule.usesBeacon) {
        appendLine()
        append("function _draw(uint256 i, bytes32 _${BEACON_VALUE.name}) internal")
        block {
            schedule.draws.forEachIndexed { k, draw ->
                val keyword = if (k == 0) "if" else "} else if"
                appendLine("$keyword (i == ${draw.node}) {")
                append(buildString { draw.body.forEach { renderStmt(it) } }.trimEnd().prependIndent("    "))
                appendLine()
            }
            appendLine("}")
        }
    }
}

/**
 * Fill the audit hooks of the schedule infrastructure: with an audit, play
 * records readiness blocks, anchors their hashes, charges a role that lets
 * its own commitment expire, and notes when play ended; without one, the
 * hooks are empty.
 */
private fun String.withAudit(audit: EvmAudit?): String {
    val hooks = mapOf(
        // A node is anchored even when it resolves here: a move made in time
        // but included after the deadline must still find its context.
        "@@SETTLE_ANCHOR@@" to listOf("if (readyAt[i] != 0) _anchor(i);"),
        "@@SETTLE_END@@" to listOf("if (endedAt == 0 && (prefix == NODE_COUNT || aborted)) endedAt = block.timestamp;"),
        "@@READY_BLOCK@@" to listOf("readyBlock[i] = block.number;"),
        "@@MISSED_BINDING@@" to listOf("if (_isCommitment(i)) _charge(owner);"),
        "@@END_MOVE@@" to listOf("_settle();"),
    )
    return hooks.entries.fold(this) { text, (hook, code) ->
        // Each inserted line is indented like the line that holds the hook.
        text.replace(Regex("(?m)^( *)(.*)" + hook)) { m ->
            val indent = m.groupValues[1]
            indent + m.groupValues[2] +
                if (audit == null) "" else code.joinToString("") { line -> "\n" + indent + line }
        }
    }
}

/**
 * The terminal audit: bonds, readiness contexts, the charge for a missed
 * binding, and evidence checking by content.
 */
private fun StringBuilder.renderAudit(contract: EvmContract, audit: EvmAudit) {
    val roleEnum = contract.enums.single { it.name == roleEnumName }
    appendLine("""
        uint256 constant public AUDIT_WINDOW = ${audit.windowSeconds};
        /// Block in which each node became ready, and that block's hash once known.
        /// A move must carry the hash, so a signed move proves it was made after that block.
        mapping(uint256 => uint256) public readyBlock;
        mapping(uint256 => bytes32) public readyHash;
        /// Whether a role's bond was burned.
        mapping(Role => bool) public charged;
        /// When play was seen to end; the audit window starts here (0 = still playing).
        uint256 public endedAt;
    """.trimIndent())
    appendLine()
    renderPureTable("_bond", "uint256", roleEnum.values.map { v ->
        audit.bonds.entries.singleOrNull { it.key.name == v }?.value?.toString() ?: "0"
    }, key = "Role role", index = { i -> "role == Role.${roleEnum.values[i]}" })
    renderPureTable("_isCommitment", "bool", contract.schedule.nodes.map { it.commitment.toString() })
    appendLine("""
        /// Snapshot the hash of node `i`'s readiness block, once the block is sealed.
        /// A hash that aged out of `blockhash` is re-anchored at the current block.
        function _anchor(uint256 i) internal {
            if (readyHash[i] != bytes32(0) || readyBlock[i] >= block.number) return;
            bytes32 h = blockhash(readyBlock[i]);
            if (h != bytes32(0)) {
                readyHash[i] = h;
            } else {
                readyBlock[i] = block.number;
            }
        }

        /// Burn a role's bond, once.
        function _charge(Role role) internal {
            if (charged[role]) return;
            charged[role] = true;
            (bool ok, ) = payable(address(0)).call{value: _bond(role)}("");
            require(ok, "burn failed");
        }

        /// Evidence: a transaction signed by a game account. `unsignedTx` is the exact
        /// payload the signature covers (a legacy RLP list, or a type byte and a list).
        /// Unless its content is permitted in the phase it names, the signer's bond is burned.
        function report(bytes calldata unsignedTx, uint8 yParity, bytes32 r, bytes32 s) external {
            require(endedAt != 0 && block.timestamp <= endedAt + AUDIT_WINDOW, "audit closed");
            address signer = ecrecover(keccak256(unsignedTx), 27 + yParity, r, s);
            require(signer != address(0), "bad signature");
            Role role = roles[signer];
            require(_bond(role) != 0, "not an audited account");
            require(!_permittedTransaction(signer, unsignedTx), "permitted traffic");
            _charge(role);
        }

        /// A transaction is permitted only as a plain call to this contract (no access
        /// list, blobs or authorizations, which could carry data) with permitted content.
        function _permittedTransaction(address signer, bytes calldata t) internal view returns (bool) {
            (bool plain, address to, uint256 value, bytes calldata data) = _callOf(t);
            if (!plain || to != address(this)) return false;
            try this.isPermitted(signer, value, data) returns (bool ok) {
                return ok;
            } catch {
                return false;
            }
        }

        /// Destination, value and calldata of a transaction payload, and whether it
        /// is plain: legacy, or type 1 or 2 with an empty access list.
        function _callOf(bytes calldata t) internal pure returns (bool plain, address to, uint256 value, bytes calldata data) {
            uint8 kind = uint8(t[0]);
            uint256 list;
            uint256 toIndex;
            if (kind >= 0xc0) {
                (list, toIndex) = (0, 3);
            } else if (kind == 1) {
                (list, toIndex) = (1, 4);
            } else if (kind == 2) {
                (list, toIndex) = (1, 5);
            } else {
                return (false, address(0), 0, t[0:0]);
            }
            (uint256 toStart, uint256 toLength) = _rlpItem(t, list, toIndex);
            (uint256 valueStart, uint256 valueLength) = _rlpItem(t, list, toIndex + 1);
            (uint256 dataStart, uint256 dataLength) = _rlpItem(t, list, toIndex + 2);
            plain = true;
            if (kind != 0 && kind < 0xc0) {
                (, uint256 accessLength) = _rlpItem(t, list, toIndex + 3);
                plain = accessLength == 0;
            }
            to = toLength == 20 ? address(bytes20(t[toStart:toStart + 20])) : address(0);
            value = _bigEndian(t[valueStart:valueStart + valueLength]);
            data = t[dataStart:dataStart + dataLength];
        }

        /// Content offset and length of item `index` of the RLP list at `list`.
        function _rlpItem(bytes calldata t, uint256 list, uint256 index) internal pure returns (uint256, uint256) {
            (uint256 pos, uint256 length) = _rlpHeader(t, list);
            uint256 end = pos + length;
            for (uint256 k = 0; ; k++) {
                require(pos < end, "short list");
                (uint256 start, uint256 size) = _rlpHeader(t, pos);
                if (k == index) return (start, size);
                pos = start + size;
            }
        }

        /// Content offset and length of the RLP item at `pos`.
        function _rlpHeader(bytes calldata t, uint256 pos) internal pure returns (uint256, uint256) {
            uint256 b = uint8(t[pos]);
            if (b < 0x80) return (pos, 1);
            if (b < 0xb8) return (pos + 1, b - 0x80);
            if (b < 0xc0) return (pos + 1 + (b - 0xb7), _bigEndian(t[pos + 1:pos + 1 + (b - 0xb7)]));
            if (b < 0xf8) return (pos + 1, b - 0xc0);
            return (pos + 1 + (b - 0xf7), _bigEndian(t[pos + 1:pos + 1 + (b - 0xf7)]));
        }

        function _bigEndian(bytes calldata x) internal pure returns (uint256 v) {
            for (uint256 k = 0; k < x.length; k++) v = (v << 8) | uint8(x[k]);
        }
    """.trimIndent())
    appendLine()
    renderPermitted(contract)
}

/**
 * `isPermitted(actor, value, data)`: whether a call to this contract, signed by
 * `actor`, is permitted in the phase it names. A game account may call
 * `settle()`, its own withdrawal, and the moves of its own nodes. A move is
 * permitted when its context is the readiness hash of its node (so it was made
 * once the node was granted) and its content passes the move's checks: the
 * domain, the guard, and, for an opening, the commitment. Its timing and
 * whether it was included do not matter. Calldata must be canonical: nothing
 * may ride along after the arguments.
 */
private fun StringBuilder.renderPermitted(contract: EvmContract) {
    val owners = contract.schedule.nodes.map { it.owner }
    append("function isPermitted(address actor, uint256 value, bytes calldata data) external view returns (bool)")
    block {
        appendLine("if (data.length < 4) return false;")
        appendLine("bytes4 selector = bytes4(data[0:4]);")
        appendLine("bytes calldata args = data[4:];")
        appendLine("if (selector == this.settle.selector) return value == 0 && args.length == 0;")
        contract.withdrawals.forEach { w ->
            appendLine("if (selector == this.${w.name}.selector) return value == 0 && args.length == 0 && roles[actor] == $roleEnumName.${w.role.name};")
        }
        contract.actions.forEach { a ->
            appendLine("if (selector == this.${a.name}.selector) return value == ${a.value} && _permitted_${a.name}(actor, args);")
        }
        appendLine("return false;")
    }
    appendLine()
    contract.actions.forEach { a ->
        require(a.inputs.all { it.type in setOf(Int256, Uint256, Bool, Bytes32) }) { "${a.name} has a dynamic input" }
        val owner = owners[a.node]
        append("function _permitted_${a.name}(address actor, bytes calldata args) internal view returns (bool)")
        block {
            appendLine("if (args.length != ${32 * a.inputs.size}) return false;")
            appendLine("if (roles[actor] != $roleEnumName.${owner.name}) return false;")
            if (a.inputs.isNotEmpty()) {
                val names = a.inputs.joinToString(", ") { "${renderType(it.type)} ${renderExpr(Var(it.name))}" }
                val types = a.inputs.joinToString(", ") { renderType(it.type) }
                appendLine("($names) = abi.decode(args, ($types));")
            }
            if (a.inputs.any { it.name == CONTEXT_PARAM }) {
                val ctx = renderExpr(Var(CONTEXT_PARAM))
                appendLine("if ($ctx == bytes32(0) || $ctx != readyHash[${a.node}]) return false;")
            }
            a.guards.forEach { appendLine("if (!(${renderExpr(it)})) return false;") }
            a.body.filterIsInstance<CheckReveal>().forEach { check ->
                val payload = check.payload.joinToString(", ") { renderExpr(it) }
                appendLine("if (_commitmentHash($roleEnumName.${check.role.name}, actor, abi.encode($payload)) != ${renderExpr(check.commitment)}) return false;")
            }
            appendLine("return true;")
        }
        appendLine()
    }
}

/** A pure lookup `name(i)` over schedule positions, as an if-chain. */
private fun StringBuilder.renderPureTable(
    name: String,
    type: String,
    values: List<String>,
    key: String = "uint256 i",
    index: (Int) -> String = { i -> "i == $i" },
) {
    append("function $name($key) internal pure returns ($type)")
    block {
        values.dropLast(1).forEachIndexed { i, v ->
            appendLine("if (${index(i)}) return $v;")
        }
        appendLine("return ${values.last()};")
    }
    appendLine()
}

private fun StringBuilder.renderConstructor(schedule: EvmSchedule, init: List<EvmStmt>, audit: EvmAudit?) {
    append(if (schedule.usesBeacon) "constructor(IVegasBeacon beacon)" else "constructor()")
    block {
        appendLine("deployedAt = block.timestamp;")
        if (schedule.usesBeacon) appendLine("BEACON = beacon;")
        if (audit != null) {
            // Source nodes are ready at deployment; their moves carry the deployment block's hash.
            schedule.nodes.withIndex().filter { it.value.predecessors.isEmpty() }.forEach { (i, _) ->
                appendLine("readyAt[$i] = block.timestamp;")
                appendLine("readyBlock[$i] = block.number;")
            }
        }
        init.forEach { renderStmt(it) }
    }
}

private fun StringBuilder.renderAction(a: EvmAction, audit: EvmAudit?) {
    val inputs = a.inputs.joinToString(", ") { "${renderType(it.type)} ${renderExpr(Var(it.name))}" }
    val mutability = if (a.payable) " payable" else ""

    append("function ${a.name}($inputs) public$mutability")
    block {
        appendLine("_beginMove(${a.node}, $roleEnumName.${a.invokedBy});")
        if (audit != null) {
            appendLine("require(${renderExpr(Var(CONTEXT_PARAM))} == readyHash[${a.node}], \"stale context\");")
        }
        a.guards.forEach { guard ->
            renderStmt(Require(guard, "domain"))
        }
        a.body.forEach { renderStmt(it) }
        appendLine("_endMove(${a.node});")
    }
    appendLine()
}

private fun StringBuilder.renderWithdrawal(w: EvmWithdrawal, audit: EvmAudit?) {
    append("function ${w.name}() public")
    block {
        appendLine("_settle();")
        appendLine("require(roles[msg.sender] == $roleEnumName.${w.role.name}, \"bad role\");")
        appendLine("require(!claimed_${w.role.name}, \"already claimed\");")
        if (audit != null) {
            appendLine("require(endedAt != 0 && block.timestamp > endedAt + AUDIT_WINDOW, \"audit open\");")
        }
        appendLine("int256 payout;")
        appendLine("if (aborted) {")
        appendLine("    payout = ${roleJoined(w.role.name)} ? int256(${w.refund}) : int256(0);")
        appendLine("} else {")
        appendLine("    require(settledPrefix == NODE_COUNT, \"game not finished\");")
        appendLine("    payout = ${renderPayoffExpr(w.payout)};")
        appendLine("}")
        if (audit != null) {
            appendLine("if (${roleJoined(w.role.name)} && !charged[$roleEnumName.${w.role.name}]) payout += int256(${audit.bonds.getValue(w.role)});")
        }
        appendLine("claimed_${w.role.name} = true;")
        appendLine("if (payout > 0) {")
        appendLine("    (bool ok, ) = payable(${roleAddr(w.role.name)}).call{value: uint256(payout)}(\"\");")
        appendLine("    require(ok, \"ETH send failed\");")
        appendLine("}")
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
    is AbiEncodeRaw -> {
        val args = e.args.joinToString(", ") { renderExpr(it) }
        "abi.encode($args)"
    }
    is EnumValue -> "${e.enumName}.${e.value}"
    is Cast -> "${renderType(e.type)}(${renderExpr(e.arg)})"
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

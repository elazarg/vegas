package vegas.eth

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.backend.evm.*
import vegas.ir.*
import vegas.runtime.*

/**
 * GameRuntime implementation that deploys Solidity contracts to Anvil
 * and plays games via Ethereum transactions.
 *
 * @param rpc JSON-RPC client connected to Anvil
 * @param accounts Pre-funded accounts available for role assignment
 * @param audit Terminal-audit policy of the deployed contract, if any
 */
class EthereumRuntime(
    private val rpc: EthJsonRpc,
    private val accounts: List<String>,
    private val audit: AuditPolicy? = null,
) : GameRuntime {

    override fun deploy(game: GameIR): GameSession {
        // 1. Compile to Solidity
        val evmContract = compileToEvm(game, audit)
        val solidity = generateSolidity(evmContract)

        // 2. Compile with solc
        val compiled = SolcCompiler.compile(solidity, game.name)

        // 3. Deploy to Anvil, with a test beacon if the game draws
        val deployer = accounts[0]
        val beacon = if (evmContract.schedule.usesBeacon) MockBeacon.deploy(rpc, deployer) else null
        val constructorArgs = beacon?.let { AbiCodec.encodeAddress(it) } ?: byteArrayOf()
        val receipt = rpc.sendAndWait(
            from = deployer,
            data = compiled.bytecode + Hex.encode(constructorArgs).removePrefix("0x"),
            functionName = "constructor(${game.name})",
        )

        val contractAddress = receipt.contractAddress
            ?: error("Deploy of ${game.name} did not return a contract address")

        // 4. Build role -> account mapping
        // Assign accounts in order: deployer uses accounts[0], then roles get accounts[1..N]
        val roleList = (game.roles + game.chanceRoles).toList().sortedBy { it.name }
        val roleAccounts = mutableMapOf<RoleId, String>()
        roleList.forEachIndexed { idx, role ->
            roleAccounts[role] = accounts[idx + 1]
        }

        return EthereumSession(
            rpc = rpc,
            game = game,
            evmContract = evmContract,
            contractAddress = contractAddress,
            roleAccounts = roleAccounts,
            beacon = beacon,
            operator = deployer,
        )
    }
}

/**
 * A game session backed by a deployed Solidity contract.
 */
class EthereumSession(
    val rpc: EthJsonRpc,
    private val game: GameIR,
    private val evmContract: EvmContract,
    val contractAddress: String,
    val roleAccounts: Map<RoleId, String>,
    private val beacon: String?,
    private val operator: String,
) : GameSession {

    /** Role enum values: None=0, then roles in declaration order (matching Solidity enum). */
    private val roleEnumValues: Map<RoleId, Int> = buildMap {
        val allRoles = (game.roles + game.chanceRoles).toList()
        allRoles.forEachIndexed { idx, role -> put(role, idx + 1) }
    }

    /** Map from NodeId to EvmAction for lookup. */
    private val actionMap: Map<NodeId, EvmAction> = evmContract.actions.associateBy { it.actionId }

    /** Track which actions have been submitted. */
    private val completedActions = mutableSetOf<NodeId>()

    /** Salts used for commit-reveal. Key: FieldRef -> (salt, clearValue). */
    private val commitSecrets = mutableMapOf<FieldRef, Pair<Long, AbiValue>>()

    /** Track current state — use semantic model in parallel. */
    private val localSession = LocalSession(game)

    override fun legalMoves(): List<GameMove> = localSession.legalMoves()

    /** Roles that have quit; their later nodes resolve without a move. */
    private val quitRoles = mutableSetOf<RoleId>()

    /** Frontier in which a fresh quit happened; its deadline passes once play leaves it. */
    private var quitFrontier: Set<NodeId>? = null

    override fun submitMove(move: GameMove) {
        // Play leaving a frontier with a fresh quit lets that quitter's deadline pass.
        quitFrontier?.let { frontier -> if (move.actionId !in frontier) letDeadlinesPass() }

        // A quit is not a transaction: the role stays silent until its deadline.
        if (move.assignments.values.any { it is Expr.Const.Quit }) {
            if (quitRoles.add(move.role)) quitFrontier = localSession.enabled()
            localSession.submitMove(move)
            return
        }

        // A private draw is the player's own knowledge: nothing happens on chain.
        if (evmContract.schedule.nodes.none { it.actionId == move.actionId }) {
            localSession.submitMove(move)
            return
        }

        if (evmContract.schedule.nodes[evmContract.schedule.indexOf(move.actionId)].kind == EvmNodeKind.DRAW) {
            submitDraw(move)
            localSession.submitMove(move)
            return
        }

        val action = actionMap[move.actionId]
            ?: error("No EVM action for NodeId ${move.actionId}")

        val role = move.role
        val account = roleAccounts[role]
            ?: error("No account assigned for role $role")

        when (move.visibility) {
            Visibility.PUBLIC -> submitPublicOrJoin(action, move, account)
            Visibility.COMMIT -> submitCommit(action, move, account)
            Visibility.REVEAL -> submitReveal(action, move, account)
        }

        completedActions.add(move.actionId)

        // Keep local session in sync
        localSession.submitMove(move)
    }

    override fun isTerminal(): Boolean = localSession.isTerminal()

    override fun payoffs(): Map<RoleId, Int> {
        require(isTerminal()) { "Cannot compute payoffs: game is not terminal" }
        return executeWithdrawals().mapValues { (_, v) -> v.toInt() }
    }

    /**
     * Execute withdrawals and return actual payoffs from the contract.
     * Uses balance snapshots to determine exact payout amounts.
     * Accounts for gas costs by using Anvil's zero-base-fee mode.
     * With a terminal audit, the audit window passes first, and the payoffs
     * are reported net of the role's bond (the bond is returned unless burned).
     */
    fun executeWithdrawals(): Map<RoleId, Long> {
        if (quitFrontier != null) letDeadlinesPass()
        evmContract.audit?.let { audit ->
            settle()
            rpc.advanceTime(audit.windowSeconds.toLong() + 1)
        }
        val payoffs = mutableMapOf<RoleId, Long>()

        for (role in game.payoffs.keys) {
            val account = roleAccounts[role] ?: continue

            val balanceBefore = rpc.getBalance(account)

            val selector = AbiCodec.functionSelector("withdraw_${role.name}()")
            val calldata = Hex.encode(selector)

            // Every role joined and every node is resolved, so no withdrawal may revert.
            rpc.sendAndWait(
                from = account,
                to = contractAddress,
                data = calldata,
                functionName = "withdraw_${role.name}()",
            )

            val balanceAfter = rpc.getBalance(account)
            // Balance delta may be negative due to gas costs; for small payoffs
            // use BigInteger subtraction then convert to Long
            payoffs[role] = (balanceAfter - balanceBefore).toLong() - (evmContract.audit?.bonds?.get(role) ?: 0)
        }

        return payoffs
    }

    /** Let every pending deadline pass, so the silent roles' nodes expire. */
    private fun letDeadlinesPass() {
        rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)
        quitFrontier = null
    }

    /**
     * Everyone still in the game stops playing: let deadlines pass, one at a
     * time, until every node is resolved (or the instance is aborted).
     */
    fun letRemainingDeadlinesPass() {
        quitFrontier = null
        repeat(evmContract.schedule.nodes.size + 1) {
            settle()
            if (view("settledPrefix()") == evmContract.schedule.nodes.size.toLong() || view("aborted()") != 0L) return
            rpc.advanceTime(EvmConstants.TIMEOUT_SECONDS.toLong() + 1)
        }
        error("schedule did not resolve")
    }

    private fun view(signature: String): Long = rpc.ethCall(operator, contractAddress,
        Hex.encode(AbiCodec.functionSelector(signature))).removePrefix("0x").toBigInteger(16).toLong()

    fun settle() {
        rpc.sendAndWait(
            from = operator,
            to = contractAddress,
            data = Hex.encode(AbiCodec.functionSelector("settle()")),
            functionName = "settle()",
        )
    }

    fun readyAt(node: Int): Long = viewAt("readyAt(uint256)", node)

    private fun viewAt(signature: String, node: Int): Long = rpc.ethCall(operator, contractAddress,
        Hex.encode(AbiCodec.functionSelector(signature) + AbiCodec.encodeUint256(node.toLong())))
        .removePrefix("0x").toBigInteger(16).toLong()

    /**
     * The readiness context an honest client binds into an audited move: the
     * hash of the block in which the node became ready, once that block is sealed.
     */
    fun contextFor(node: Int): ByteArray {
        if (viewAt("readyBlock(uint256)", node) == 0L) settle()
        val block = viewAt("readyBlock(uint256)", node)
        check(block != 0L) { "node $node is not ready" }
        if (block >= rpc.latestBlockNumber()) rpc.evmMine()
        return rpc.blockHash(block)
    }

    /** Arguments of [action]: the readiness context where required, then [values] for the rest. */
    private fun arguments(action: EvmAction, values: (EvmParam) -> AbiValue): List<AbiValue> =
        action.inputs.map { param ->
            if (param.name == CONTEXT_PARAM) AbiValue.Bytes32(contextFor(action.node)) else values(param)
        }

    /** The entry point of a node, and its ABI signature (for off-script transactions). */
    fun action(id: NodeId): EvmAction = actionMap.getValue(id)
    fun functionSignature(id: NodeId): String = signature(action(id))

    /** The salt and clear value a role committed for [field] (its private knowledge). */
    fun secret(field: FieldRef): Pair<Long, AbiValue> = commitSecrets.getValue(field)

    private fun signature(action: EvmAction): String =
        "${action.name}(${action.inputs.joinToString(",") { evmTypeToSolidity(it.type) }})"

    /**
     * A draw happens without a player: publish a beacon round for the node's
     * readiness time whose output maps to the model's value, then settle.
     */
    private fun submitDraw(move: GameMove) {
        val node = evmContract.schedule.indexOf(move.actionId)
        settle()
        val ready = readyAt(node)
        check(ready != 0L) { "draw ${move.actionId} is not ready" }
        val dist = requireNotNull(game.dag.sampleSpec(move.actionId)?.dist) { "draw ${move.actionId} has no distribution" }
        val value = move.assignments.values.single()
        val output = MockBeacon.outputDrawing(contractAddress, node, dist, value)
        MockBeacon.publish(rpc, operator, requireNotNull(beacon), ready, output)
        if (rpc.latestBlockTimestamp() <= ready) rpc.advanceTime(1)
        settle()
    }

    // ========== Private: Submit methods ==========

    private fun submitPublicOrJoin(action: EvmAction, move: GameMove, account: String) {
        val isJoin = action.payable

        val funcSig = signature(action)
        val selector = AbiCodec.functionSelector(funcSig)

        // Encode arguments
        val args = arguments(action) { param ->
            val varId = extractVarId(param.name)
            val value = move.assignments[varId]
                ?: error("Missing assignment for ${param.name} in move for ${action.name}")
            constToAbiValue(value, param.type)
        }

        val calldata = Hex.encode(AbiCodec.encodeCall(selector, *args.toTypedArray()))

        // Compute value (deposit, plus the audit bond, for join actions)
        val weiValue = if (isJoin) {
            val deposit = game.dag.spec(move.actionId).join?.deposit?.v
                ?: error("Join action ${action.name} has no deposit")
            val bond = evmContract.audit?.bonds?.get(move.role) ?: 0
            "0x" + (deposit + bond).toLong().toString(16)
        } else {
            "0x0"
        }

        rpc.sendAndWait(
            from = account,
            to = contractAddress,
            data = calldata,
            value = weiValue,
            functionName = funcSig,
        )
    }

    private fun submitCommit(action: EvmAction, move: GameMove, account: String) {
        // For commit actions, we need to:
        // 1. Generate a salt for each parameter
        // 2. Compute the commitment hash
        // 3. Store the salt for later reveal
        // 4. Submit the commitment hash

        val roleEnum = roleEnumValues[move.role]
            ?: error("No enum value for role ${move.role}")

        // One salt per commit action: its reveal checks every parameter against one salt.
        val salt = CommitmentManager.generateSalt()
        val commitmentArgs = arguments(action) { param ->
            val varId = extractVarId(param.name)
            // The semantic model wraps committed values in Hidden()
            val clearValue = when (val hiddenValue = move.assignments[varId]) {
                is Expr.Const.Hidden -> hiddenValue.inner
                else -> hiddenValue ?: error("Missing assignment for $varId")
            }

            val clearAbi = constToAbiValue(clearValue, resolveBaseType(varId, move.role))
            val payload = CommitmentManager.encodePayload(clearAbi, AbiValue.Uint256(salt))

            val commitment = CommitmentManager.commitmentHash(
                contractAddress = contractAddress,
                roleEnumValue = roleEnum,
                actorAddress = account,
                payload = payload,
            )

            commitSecrets[FieldRef(move.role, varId)] = Pair(salt, clearAbi)
            AbiValue.Bytes32(commitment)
        }

        // Build calldata
        val funcSig = signature(action)
        val selector = AbiCodec.functionSelector(funcSig)
        val calldata = Hex.encode(AbiCodec.encodeCall(selector, *commitmentArgs.toTypedArray()))

        rpc.sendAndWait(
            from = account,
            to = contractAddress,
            data = calldata,
            functionName = funcSig,
        )
    }

    private fun submitReveal(action: EvmAction, move: GameMove, account: String) {
        // For reveal actions, we need to submit the clear value + salt
        // The action inputs are: value params + salt param

        var storedSalt: Long? = null
        val args = arguments(action) { param ->
            if (param.name == VarId("salt")) {
                AbiValue.Uint256(storedSalt ?: error("No salt found for reveal"))
            } else {
                val fieldRef = FieldRef(move.role, extractVarId(param.name))
                val (salt, clearAbi) = commitSecrets[fieldRef]
                    ?: error("No stored secret for $fieldRef — was commit submitted?")
                storedSalt = salt
                clearAbi
            }
        }

        // Build calldata
        val funcSig = signature(action)
        val selector = AbiCodec.functionSelector(funcSig)
        val calldata = Hex.encode(AbiCodec.encodeCall(selector, *args.toTypedArray()))

        rpc.sendAndWait(
            from = account,
            to = contractAddress,
            data = calldata,
            functionName = funcSig,
        )
    }

    // ========== Helpers ==========

    /** Extract the VarId from an EvmParam name, stripping hidden_ prefix and underscore prefix. */
    private fun extractVarId(paramName: VarId): VarId {
        val name = paramName.name
            .removePrefix("hidden_")
        return VarId(name)
    }

    /** Resolve the base EVM type for a variable (used for commit actions that use bytes32). */
    private fun resolveBaseType(varId: VarId, role: RoleId): EvmType {
        // Find the reveal action or public action for this field to get the actual type
        for (action in evmContract.actions) {
            if (action.actionId.first != role) continue
            val meta = game.dag.meta(action.actionId)
            if (meta.kind == Visibility.REVEAL || meta.kind == Visibility.PUBLIC) {
                val param = action.inputs.find { extractVarId(it.name) == varId }
                if (param != null) return param.type
            }
        }
        // Fallback: look at the DAG spec
        val dagParam = game.dag.actions
            .filter { it.first == role }
            .flatMap { game.dag.params(it) }
            .find { it.name == varId }
        return when (dagParam?.type) {
            is Type.BoolType -> EvmType.Bool
            is Type.IntType, is Type.RangeType -> EvmType.Int256
            null -> EvmType.Int256
        }
    }

    private fun constToAbiValue(value: Expr.Const, type: EvmType): AbiValue = when (type) {
        EvmType.Bool -> AbiValue.Bool((value as Expr.Const.BoolVal).v)
        EvmType.Int256 -> AbiValue.Int256((value as Expr.Const.IntVal).v)
        EvmType.Uint256 -> AbiValue.Uint256((value as Expr.Const.IntVal).v.toLong())
        EvmType.Bytes32 -> error("bytes32 values should be handled via commitment path")
        else -> error("Unsupported EVM type for value encoding: $type")
    }

    private fun evmTypeToSolidity(type: EvmType): String = when (type) {
        EvmType.Int256 -> "int256"
        EvmType.Uint256 -> "uint256"
        EvmType.Bool -> "bool"
        EvmType.Address -> "address"
        EvmType.Bytes32 -> "bytes32"
        is EvmType.Bytes -> "bytes"
        is EvmType.Mapping -> error("Mapping type not valid as function parameter")
        is EvmType.EnumType -> error("Enum type not valid as raw function parameter")
    }
}

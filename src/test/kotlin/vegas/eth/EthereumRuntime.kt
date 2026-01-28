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
 */
class EthereumRuntime(
    private val rpc: EthJsonRpc,
    private val accounts: List<String>,
) : GameRuntime {

    override fun deploy(game: GameIR): GameSession {
        // 1. Compile to Solidity
        val evmContract = compileToEvm(game)
        val solidity = generateSolidity(evmContract)

        // 2. Compile with solc
        val compiled = SolcCompiler.compile(solidity, game.name)

        // 3. Deploy to Anvil
        val deployer = accounts[0]
        val receipt = rpc.sendAndWait(
            from = deployer,
            data = compiled.bytecode,
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
    private val contractAddress: String,
    private val roleAccounts: Map<RoleId, String>,
) : GameSession {

    /** Role enum values: None=0, then roles in declaration order (matching Solidity enum). */
    private val roleEnumValues: Map<RoleId, Int> = buildMap {
        val allRoles = (game.roles + game.chanceRoles).toList()
        allRoles.forEachIndexed { idx, role -> put(role, idx + 1) }
    }

    /** Map from ActionId to EvmAction for lookup. */
    private val actionMap: Map<ActionId, EvmAction> = evmContract.actions.associateBy { it.actionId }

    /** Track which actions have been submitted. */
    private val completedActions = mutableSetOf<ActionId>()

    /** Salts used for commit-reveal. Key: FieldRef -> (salt, clearValue). */
    private val commitSecrets = mutableMapOf<FieldRef, Pair<Long, AbiValue>>()

    /** Track current state — use semantic model in parallel. */
    private val localSession = LocalSession(game)

    override fun legalMoves(): List<GameMove> = localSession.legalMoves()

    override fun submitMove(move: GameMove) {
        val action = actionMap[move.actionId]
            ?: error("No EVM action for ActionId ${move.actionId}")

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
     */
    fun executeWithdrawals(): Map<RoleId, Long> {
        val payoffs = mutableMapOf<RoleId, Long>()

        for (role in game.roles + game.chanceRoles) {
            val account = roleAccounts[role] ?: continue

            val balanceBefore = rpc.getBalance(account)

            val selector = AbiCodec.functionSelector("withdraw_${role.name}()")
            val calldata = Hex.encode(selector)

            try {
                rpc.sendAndWait(
                    from = account,
                    to = contractAddress,
                    data = calldata,
                    functionName = "withdraw_${role.name}()",
                )
            } catch (_: TxRevertedException) {
                // Withdraw may revert if payout is 0 or role didn't play
                payoffs[role] = 0
                continue
            }

            val balanceAfter = rpc.getBalance(account)
            // Balance delta may be negative due to gas costs; for small payoffs
            // use BigInteger subtraction then convert to Long
            payoffs[role] = (balanceAfter - balanceBefore).toLong()
        }

        return payoffs
    }

    // ========== Private: Submit methods ==========

    private fun submitPublicOrJoin(action: EvmAction, move: GameMove, account: String) {
        val isJoin = action.payable

        // Build function signature for selector computation
        val paramTypes = action.inputs.map { evmTypeToSolidity(it.type) }
        val funcSig = "${action.name}(${paramTypes.joinToString(",")})"
        val selector = AbiCodec.functionSelector(funcSig)

        // Encode arguments
        val args = action.inputs.map { param ->
            val varId = extractVarId(param.name)
            val value = move.assignments[varId]
                ?: error("Missing assignment for ${param.name} in move for ${action.name}")
            constToAbiValue(value, param.type)
        }

        val calldata = Hex.encode(AbiCodec.encodeCall(selector, *args.toTypedArray()))

        // Compute value (deposit for join actions)
        val weiValue = if (isJoin) {
            val deposit = game.dag.spec(move.actionId).join?.deposit?.v
                ?: error("Join action ${action.name} has no deposit")
            "0x" + deposit.toLong().toString(16)
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

        // Build commitment hashes for each parameter
        val commitmentArgs = mutableListOf<AbiValue>()

        for (param in action.inputs) {
            val varId = extractVarId(param.name)
            // The semantic model wraps committed values in Hidden()
            val clearValue = when (val hiddenValue = move.assignments[varId]) {
                is Expr.Const.Hidden -> hiddenValue.inner
                else -> hiddenValue ?: error("Missing assignment for $varId")
            }

            val salt = CommitmentManager.generateSalt()
            val clearAbi = constToAbiValue(clearValue, resolveBaseType(varId, move.role))
            val payload = CommitmentManager.encodePayload(clearAbi, AbiValue.Uint256(salt))

            val commitment = CommitmentManager.commitmentHash(
                contractAddress = contractAddress,
                roleEnumValue = roleEnum,
                actorAddress = account,
                payload = payload,
            )

            commitSecrets[FieldRef(move.role, varId)] = Pair(salt, clearAbi)
            commitmentArgs.add(AbiValue.Bytes32(commitment))
        }

        // Build calldata
        val paramTypes = action.inputs.map { evmTypeToSolidity(it.type) }
        val funcSig = "${action.name}(${paramTypes.joinToString(",")})"
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

        val args = mutableListOf<AbiValue>()

        // All params except the last one (which is the salt)
        val valueParams = action.inputs.dropLast(1)  // Last is always "salt"
        var storedSalt: Long? = null

        for (param in valueParams) {
            val varId = extractVarId(param.name)
            val fieldRef = FieldRef(move.role, varId)
            val (salt, clearAbi) = commitSecrets[fieldRef]
                ?: error("No stored secret for $fieldRef — was commit submitted?")

            args.add(clearAbi)
            storedSalt = salt
        }

        // Add salt as last argument
        args.add(AbiValue.Uint256(storedSalt ?: error("No salt found for reveal")))

        // Build calldata
        val paramTypes = action.inputs.map { evmTypeToSolidity(it.type) }
        val funcSig = "${action.name}(${paramTypes.joinToString(",")})"
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
            is Type.IntType, is Type.SetType -> EvmType.Int256
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

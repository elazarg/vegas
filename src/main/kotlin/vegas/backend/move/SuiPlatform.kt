package vegas.backend.move

import vegas.ir.GameIR

object SuiPlatform : MovePlatform {
    override val name = "sui"

    override val imports = setOf(
        MoveImport("sui", "object"),
        MoveImport("sui", "transfer"),
        MoveImport("sui", "tx_context"),
        MoveImport("sui", "coin"),
        MoveImport("sui", "balance"),
        MoveImport("sui", "clock"),
        MoveImport("sui", "event"),
        MoveImport("std", "vector"),
        MoveImport("std", "bcs"),
        MoveImport("sui", "hash")
    )

    private val UID = MoveType.Struct("sui::object", "UID")
    private val TxContext = MoveType.Struct("sui::tx_context", "TxContext")
    private val Clock = MoveType.Struct("sui::clock", "Clock")

    override fun coinType(assetType: MoveType): MoveType =
        MoveType.Struct("sui::coin", "Coin", listOf(assetType))

    override fun balanceType(assetType: MoveType): MoveType =
        MoveType.Struct("sui::balance", "Balance", listOf(assetType))

    override fun instanceAbilities(): List<String> = listOf("key")

    override fun extraInstanceFields(game: GameIR): List<MoveField> {
        return listOf(MoveField("id", UID))
    }

    override fun extraInstanceInit(ctxVar: MoveExpr): Map<String, MoveExpr> {
        return mapOf("id" to MoveExpr.Call("sui::object", "new", emptyList(), listOf(ctxVar)))
    }

    override fun initFunctionParams(): List<MoveParam> {
        return listOf(MoveParam("ctx", MoveType.Ref(TxContext, true)))
    }

    override fun contextParamName(): String = "ctx"

    override fun contextParamType(isMut: Boolean): MoveType {
        return MoveType.Ref(TxContext, isMut)
    }

    override fun extraActionParams(): List<MoveParam> {
        return listOf(MoveParam("clock", MoveType.Ref(Clock, false)))
    }

    override fun createInstanceBody(ctxVar: MoveExpr, instanceVar: MoveExpr, assetType: MoveType): List<MoveStmt> {
        // sui::transfer::share_object<Asset>(instance)
        return listOf(
            MoveStmt.ExprStmt(MoveExpr.Call(
                "sui::transfer", "share_object",
                listOf(assetType),
                listOf(instanceVar)
            ))
        )
    }

    override fun getSender(ctxVar: MoveExpr): MoveExpr {
        // sui::tx_context::sender(ctx)
        return MoveExpr.Call("sui::tx_context", "sender", emptyList(), listOf(ctxVar))
    }

    override fun currentTimeExpr(clockVar: MoveExpr?): MoveExpr {
        if (clockVar == null) error("Sui requires clock for time")
        // sui::clock::timestamp_ms(clock)
        return MoveExpr.Call("sui::clock", "timestamp_ms", emptyList(), listOf(clockVar))
    }

    override fun zeroBalance(assetType: MoveType): MoveExpr {
        // sui::balance::zero<Asset>()
        return MoveExpr.Call("sui::balance", "zero", listOf(assetType), emptyList())
    }

    override fun joinBalanceStmt(potRef: MoveExpr, paymentVar: MoveExpr, assetType: MoveType): MoveStmt {
        // sui::balance::join(&mut pot, sui::coin::into_balance(payment))
        val intoBalance = MoveExpr.Call(
            "sui::coin", "into_balance",
            listOf(assetType),
            listOf(paymentVar)
        )
        return MoveStmt.ExprStmt(MoveExpr.Call(
            "sui::balance", "join",
            listOf(assetType),
            listOf(potRef, intoBalance)
        ))
    }

    override fun withdrawAndTransferStmt(
        potRef: MoveExpr,
        amount: MoveExpr,
        recipient: MoveExpr,
        ctxVar: MoveExpr,
        assetType: MoveType
    ): List<MoveStmt> {
        // let coin = coin::take(&mut pot, amount, ctx);
        // transfer::public_transfer(coin, recipient);

        return listOf(
            MoveStmt.Let("payout_coin", null, MoveExpr.Call(
                "sui::coin", "take",
                listOf(assetType),
                listOf(potRef, amount, ctxVar)
            )),
            MoveStmt.ExprStmt(MoveExpr.Call(
                "sui::transfer", "public_transfer",
                listOf(assetType),
                listOf(MoveExpr.Var("payout_coin"), recipient)
            ))
        )
    }

    override fun hash(data: MoveExpr): MoveExpr {
        // sui::hash::keccak256(data)
        return MoveExpr.Call("sui::hash", "keccak256", emptyList(), listOf(data))
    }

    // Check sender is just equality in Sui usually, unless we use Capabilities.
    // For this simple backend, sender() == address stored.
    override fun checkSender(ctxVar: MoveExpr, roleAddr: MoveExpr): MoveExpr {
        return MoveExpr.BinOp(MoveBinOp.EQ, getSender(ctxVar), roleAddr)
    }
}

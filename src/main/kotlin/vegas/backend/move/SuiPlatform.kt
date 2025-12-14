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

    private val UID = MoveType.Struct("object", "UID")
    private val TxContext = MoveType.Struct("tx_context", "TxContext")
    private val Clock = MoveType.Struct("clock", "Clock")

    override fun coinType(assetType: MoveType): MoveType =
        MoveType.Struct("coin", "Coin", listOf(assetType))

    override fun balanceType(assetType: MoveType): MoveType =
        MoveType.Struct("balance", "Balance", listOf(assetType))

    override fun instanceAbilities(): List<String> = listOf("key")

    override fun extraInstanceFields(game: GameIR): List<MoveField> {
        return listOf(MoveField("id", UID))
    }

    override fun extraInstanceInit(ctxVar: MoveExpr): Map<String, MoveExpr> {
        return mapOf("id" to MoveExpr.Call("object", "new", emptyList(), listOf(ctxVar)))
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
        // transfer::share_object(instance)
        return listOf(
            MoveStmt.ExprStmt(MoveExpr.Call(
                "transfer", "share_object",
                emptyList(),
                listOf(instanceVar)
            ))
        )
    }

    override fun getSender(ctxVar: MoveExpr): MoveExpr {
        // tx_context::sender(ctx)
        return MoveExpr.Call("tx_context", "sender", emptyList(), listOf(ctxVar))
    }

    override fun currentTimeExpr(clockVar: MoveExpr?): MoveExpr {
        if (clockVar == null) error("Sui requires clock for time")
        // clock::timestamp_ms(clock)
        return MoveExpr.Call("clock", "timestamp_ms", emptyList(), listOf(clockVar))
    }

    override fun zeroBalance(assetType: MoveType): MoveExpr {
        // balance::zero<Asset>()
        return MoveExpr.Call("balance", "zero", listOf(assetType), emptyList())
    }

    override fun coinValue(coinExpr: MoveExpr, assetType: MoveType): MoveExpr {
        // coin::value(&coin)
        return MoveExpr.Call("coin", "value", listOf(assetType), listOf(MoveExpr.Borrow(coinExpr, false)))
    }

    override fun joinBalanceStmt(potRef: MoveExpr, paymentVar: MoveExpr, assetType: MoveType): MoveStmt {
        // balance::join(&mut pot, coin::into_balance(payment))
        val intoBalance = MoveExpr.Call(
            "coin", "into_balance",
            listOf(assetType),
            listOf(paymentVar)
        )
        return MoveStmt.ExprStmt(MoveExpr.Call(
            "balance", "join",
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
                "coin", "take",
                listOf(assetType),
                listOf(potRef, amount, ctxVar)
            )),
            MoveStmt.ExprStmt(MoveExpr.Call(
                "transfer", "public_transfer",
                listOf(assetType),
                listOf(MoveExpr.Var("payout_coin"), recipient)
            ))
        )
    }

    override fun hash(data: MoveExpr): MoveExpr {
        // hash::keccak256(data)
        return MoveExpr.Call("hash", "keccak256", emptyList(), listOf(data))
    }

    override fun checkSender(ctxVar: MoveExpr, roleAddr: MoveExpr): MoveExpr {
        return MoveExpr.BinOp(MoveBinOp.EQ, getSender(ctxVar), roleAddr)
    }
}

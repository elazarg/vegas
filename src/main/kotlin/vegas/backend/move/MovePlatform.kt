package vegas.backend.move

import vegas.ir.GameIR

interface MovePlatform {
    val name: String

    // Core imports required by the platform
    val imports: Set<MoveImport>

    // Type definitions
    fun addressType(): MoveType = MoveType.Address
    fun u64Type(): MoveType = MoveType.U64
    fun boolType(): MoveType = MoveType.Bool

    fun coinType(assetType: MoveType): MoveType
    fun balanceType(assetType: MoveType): MoveType

    // Struct configuration
    fun instanceAbilities(): List<String>
    fun extraInstanceFields(game: GameIR): List<MoveField>

    // Returns map of field name to initialization expression (e.g. id -> object::new(ctx))
    fun extraInstanceInit(ctxVar: MoveExpr): Map<String, MoveExpr>

    // Function signature customization
    fun initFunctionParams(): List<MoveParam> // Params for module init

    // Params for entry functions (create_game, join, move, etc.)
    // contextVarName is usually "ctx" for Sui, "account" for Aptos
    fun contextParamName(): String
    fun contextParamType(isMut: Boolean): MoveType

    // Additional params needed for actions (e.g. Clock in Sui)
    fun extraActionParams(): List<MoveParam>

    // Code generation hooks

    // Create the game instance (e.g. share_object or move_to)
    fun createInstanceBody(
        ctxVar: MoveExpr, // Variable holding context/signer
        instanceVar: MoveExpr, // Variable holding the created struct
        assetType: MoveType
    ): List<MoveStmt>

    // Get sender/signer address
    fun getSender(ctxVar: MoveExpr): MoveExpr

    // Check if sender is authorized (e.g. signer::address_of(account) == role_addr)
    fun checkSender(ctxVar: MoveExpr, roleAddr: MoveExpr): MoveExpr

    // Get current time in ms
    // clockVar is the variable name for the clock/timestamp param if passed, or null
    fun currentTimeExpr(clockVar: MoveExpr?): MoveExpr

    // Escrow operations
    fun zeroBalance(assetType: MoveType): MoveExpr

    // Get value of a coin expression
    fun coinValue(coinExpr: MoveExpr, assetType: MoveType): MoveExpr

    // Convert payment param to balance and join to pot
    // Returns expression or statement to execute join
    fun joinBalanceStmt(
        potRef: MoveExpr, // &mut pot
        paymentVar: MoveExpr,
        assetType: MoveType
    ): MoveStmt

    // Withdraw amount from pot and transfer to recipient
    fun withdrawAndTransferStmt(
        potRef: MoveExpr, // &mut pot
        amount: MoveExpr,
        recipient: MoveExpr,
        ctxVar: MoveExpr,
        assetType: MoveType
    ): List<MoveStmt>

    // Commit/Reveal Hashing
    // Returns expression for hash(data)
    fun hash(data: MoveExpr): MoveExpr
}

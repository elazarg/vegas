package vegas.eth.tests

import io.kotest.core.annotation.EnabledIf
import io.kotest.core.spec.style.FunSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.ints.shouldBeGreaterThan
import io.kotest.matchers.longs.shouldBeGreaterThan
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import kotlinx.serialization.json.jsonPrimitive
import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.backend.evm.AuditPolicy
import vegas.eth.*
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Visibility
import vegas.runtime.GameMove
import vegas.watcher.JsonRpc
import vegas.watcher.SignedTransaction
import vegas.watcher.Watcher
import java.math.BigInteger

/**
 * The count audit and its watcher, end to end on a local chain.
 *
 * In Coordination (Battle of the Sexes) both players choose simultaneously;
 * disclosing a choice early lets Alice move first and make Bob follow her,
 * turning her worst equilibrium (4) into her best outcome (16). The watcher
 * collects that disclosure from the node's pool or the chain, and the
 * contract burns Alice's audit deposit at settlement. As in VegasCore's count
 * audit, a game account may send one well-formed move per node it owns, and
 * nothing else; a record is judged by its content and its readiness
 * credential, not by whether or when it was included. Honest play is never
 * charged, even when a move lands late; a fee bump is the same transaction;
 * the watcher cannot charge anything a player did not sign; and quitting is
 * never charged.
 */
@EnabledIf(EthToolsAvailable::class)
class EthWatcherTest : FunSpec({
    // A fresh chain per test: game accounts must be fresh, and the node's
    // accounts are reused, so earlier games' traffic would be (rightly) evidence.
    val anvil = AnvilNode()
    beforeTest { anvil.start() }
    afterTest { anvil.stop() }

    val alice = RoleId("Alice")
    val bob = RoleId("Bob")
    val policy = AuditPolicy()
    val game: GameIR = compileToIR(inlineMacros(parseExample("Coordination")))
    val evm = vegas.backend.evm.compileToEvm(game, policy)
    val deposit = evm.audit!!.deposits.getValue(alice).toLong()
    val bobsDeposit = evm.audit!!.deposits.getValue(bob).toLong()

    class Match(val rpc: EthJsonRpc, val session: EthereumSession, val watcher: Watcher) {
        val contract get() = session.contractAddress
        fun account(role: RoleId) = session.roleAccounts.getValue(role)
    }

    fun start(): Match {
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val session = EthereumRuntime(rpc, anvil.accounts, policy).deploy(game) as EthereumSession
        val watcher = Watcher(JsonRpc(anvil.rpcUrl), session.contractAddress, reporter = anvil.accounts[0],
            roles = listOf("Alice", "Bob"), fromBlock = rpc.latestBlockNumber())
        return Match(rpc, session, watcher)
    }

    /** Play [role]'s legal move whose value is [value] (null: its join), then let the watcher look. */
    fun Match.play(role: RoleId, value: Boolean? = null) {
        val move = session.legalMoves().first { m ->
            m.role == role && when (value) {
                null -> m.assignments.isEmpty()
                else -> m.assignments.values.singleOrNull().let {
                    it == Expr.Const.BoolVal(value) || it == Expr.Const.Hidden(Expr.Const.BoolVal(value))
                }
            }
        }
        session.submitMove(move)
        watcher.observe()
    }

    /** [role] stays silent at its next move until the deadline passes. */
    fun Match.quit(role: RoleId) {
        session.submitMove(session.legalMoves().first { m ->
            m.role == role && m.assignments.values.any { it is Expr.Const.Quit }
        })
    }

    fun Match.revealNode(role: RoleId) = game.dag.actions.single {
        game.dag.owner(it) == role && game.dag.kind(it) == Visibility.REVEAL
    }

    fun Match.commitNode(role: RoleId) = game.dag.actions.single {
        game.dag.owner(it) == role && game.dag.kind(it) == Visibility.COMMIT
    }

    /** [role]'s opening, bound to its node's real readiness credential, with [salt] (default: the real one). */
    fun Match.openingCalldata(role: RoleId, salt: Long? = null): String {
        val node = revealNode(role)
        val (realSalt, value) = session.secret(FieldRef(role, VarId("opera")))
        return Hex.encode(AbiCodec.encodeCall(
            AbiCodec.functionSelector(session.functionSignature(node)),
            AbiValue.Bytes32(session.credentialFor(evm.schedule.indexOf(node))), value, AbiValue.Uint256(salt ?: realSalt),
        ))
    }

    fun Match.charged(role: RoleId): Boolean {
        val index = evm.enums.single { it.name == "Role" }.values.indexOf(role.name)
        return rpc.ethCall(account(alice), contract, Hex.encode(
            AbiCodec.functionSelector("charged(uint8)") + AbiCodec.encodeUint256(index.toLong())
        )).removePrefix("0x").toBigInteger(16) == BigInteger.ONE
    }

    /** Alice's reveal, signed before it is her turn: the call data carries her choice and salt. */
    fun Match.earlyRevealCalldata(): String {
        val (salt, value) = session.secret(FieldRef(alice, VarId("opera")))
        val guessedCredential = rpc.blockHash(rpc.latestBlockNumber())
        return Hex.encode(AbiCodec.encodeCall(
            AbiCodec.functionSelector(session.functionSignature(revealNode(alice))),
            AbiValue.Bytes32(guessedCredential), value, AbiValue.Uint256(salt),
        ))
    }

    /** What Bob learns from a transaction of Alice's that carries her opening, checked against her commitment. */
    fun Match.bobReads(input: String): Boolean {
        val words = input.removePrefix("0x").drop(8).chunked(64)
        val opera = BigInteger(words[1], 16) == BigInteger.ONE
        val salt = BigInteger(words[2], 16).toLong()
        val commitment = rpc.ethCall(account(bob), contract, Hex.encode(AbiCodec.functionSelector("Alice_opera_hidden()")))
        val expected = CommitmentManager.commitmentHash(contract, 1, account(alice),
            CommitmentManager.encodePayload(AbiValue.Bool(opera), AbiValue.Uint256(salt)))
        Hex.encode(expected) shouldBe commitment
        return opera
    }

    fun Match.finish(): Pair<List<Watcher.Outcome>, Map<RoleId, Long>> {
        session.settle()
        watcher.playEnded() shouldBe true
        val outcomes = watcher.audit()
        return outcomes to session.executeWithdrawals()
    }

    test("honest play: every record is a well-formed move and deposits come back") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, false); m.play(bob, false)
        m.play(alice, false); m.play(bob, false)
        val (outcomes, payoffs) = m.finish()
        outcomes.size shouldBeGreaterThan 0
        outcomes.filter { it.charged }.shouldBeEmpty()
        outcomes.forEach { it.reason shouldContain "well-formed move" }
        payoffs shouldBe mapOf(alice to 4L, bob to 16L)
        m.watcher.unsupported.shouldBeEmpty()
    }

    test("a disclosure that is never included is collected from the pool and burns the deposit") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, true)
        // Alice broadcasts her opening while Bob still has to choose. With a
        // nonce gap it waits in the pool and is never included.
        val leak = m.rpc.sendAsync(m.account(alice), m.contract, m.earlyRevealCalldata(),
            nonce = m.rpc.nonce(m.account(alice)) + 100)
        m.watcher.observe()
        // Bob reads the pool, checks the opening against Alice's commitment, and follows her.
        val seen = m.rpc.txpool().single { it["hash"]!!.jsonPrimitive.content == leak }
        m.bobReads(seen["input"]!!.jsonPrimitive.content) shouldBe true
        m.play(bob, true)
        m.play(alice, true); m.play(bob, true)

        val (outcomes, payoffs) = m.finish()
        outcomes.single { it.tx.hash == leak }.charged shouldBe true
        // Her later opening is a second transaction for the same node; the deposit is burned once.
        outcomes.filter { it.charged }.map { it.role }.distinct() shouldBe listOf("Alice")
        outcomes.filter { "reported" in it.reason }.map { it.tx.hash } shouldBe listOf(leak)
        // Leading gained Alice 16 - 4 = 12 over her worst equilibrium; the deposit (20) exceeds it.
        payoffs shouldBe mapOf(alice to 16L - deposit, bob to 4L)
        (payoffs.getValue(alice) < 4L) shouldBe true
        m.rpc.txpool().map { it["hash"]!!.jsonPrimitive.content } shouldBe listOf(leak)
    }

    test("a disclosure that was included and rejected is collected from the chain") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, true)
        val leak = m.rpc.sendAsync(m.account(alice), m.contract, m.earlyRevealCalldata())
        m.rpc.receiptStatus(leak) shouldBe false
        m.watcher.observe()
        m.play(bob, true)
        m.play(alice, true); m.play(bob, true)

        val (outcomes, payoffs) = m.finish()
        outcomes.single { it.tx.hash == leak }.charged shouldBe true
        payoffs shouldBe mapOf(alice to 16L - deposit, bob to 4L)
    }

    test("blob and set-code transactions are evidence, whatever they call") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, true)
        // Alice discloses in a set-code transaction and again in a blob transaction.
        val setCode = Cast.sendSetCode(anvil.rpcUrl, Cast.key(1), m.contract, m.earlyRevealCalldata(),
            delegate = "0x0000000000000000000000000000000000000abc")
        val blob = Cast.sendBlob(anvil.rpcUrl, Cast.key(1), m.contract, m.earlyRevealCalldata(), "opening".toByteArray())
        m.watcher.observe()
        m.play(bob, true)
        // Bob re-sends his own well-formed commitment inside a set-code transaction.
        // Its authorization list is data outside the protocol (as a blob would be), so it is evidence too.
        val bobsCommit = m.watcher.recorded.last { it.from == m.account(bob).lowercase() }
        val wrapped = Cast.sendSetCode(anvil.rpcUrl, Cast.key(2), m.contract,
            m.rpc.txByHash(bobsCommit.hash)["input"]!!.jsonPrimitive.content, delegate = "0x0000000000000000000000000000000000000abc")
        m.watcher.observe()
        m.play(alice, true); m.play(bob, true)

        val (outcomes, payoffs) = m.finish()
        m.watcher.unsupported.shouldBeEmpty()
        outcomes.single { it.tx.hash == setCode }.charged shouldBe true
        outcomes.single { it.tx.hash == blob }.charged shouldBe true
        outcomes.single { it.tx.hash == wrapped }.charged shouldBe true
        payoffs shouldBe mapOf(alice to 16L - deposit, bob to 4L - bobsDeposit)
    }

    test("a disclosure that reaches only another node is caught only if that node's pool is watched") {
        val m = start()
        val other = AnvilNode()
        other.start(forkUrl = anvil.rpcUrl)
        try {
            m.play(alice); m.play(bob)
            m.play(alice, true)
            // The leak goes to the other node only, and waits there (nonce gap).
            val otherRpc = EthJsonRpc(other.rpcUrl)
            val leak = otherRpc.sendAsync(m.account(alice), m.contract, m.earlyRevealCalldata(),
                nonce = otherRpc.nonce(m.account(alice)) + 100)
            val wide = Watcher(JsonRpc(anvil.rpcUrl), m.contract, anvil.accounts[0], listOf("Alice", "Bob"),
                pools = listOf(JsonRpc(anvil.rpcUrl), JsonRpc(other.rpcUrl)))
            m.watcher.observe(); wide.observe()
            m.watcher.recorded.none { it.hash == leak } shouldBe true
            wide.recorded.any { it.hash == leak } shouldBe true

            m.play(bob, true)
            m.play(alice, true); m.play(bob, true)
            m.session.settle()
            m.watcher.audit().none { it.charged } shouldBe true
            wide.audit().single { it.tx.hash == leak }.charged shouldBe true
        } finally {
            other.stop()
        }
    }

    test("replaying an executed call is a second transaction for its node, and outsiders' traffic is not evidence") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, false); m.play(bob, false)
        // Bob re-sends his exact commitment call with a new nonce: it reverts, but it is a
        // second transaction for his node, and its timing alone could carry a signal.
        val bobsCommit = m.watcher.recorded.last { it.from == m.account(bob).lowercase() }
        val original = m.rpc.txByHash(bobsCommit.hash)
        val replay = m.rpc.sendAsync(m.account(bob), m.contract, original["input"]!!.jsonPrimitive.content)
        m.rpc.receiptStatus(replay) shouldBe false
        m.watcher.observe()
        m.play(alice, false); m.play(bob, false)

        // Someone outside the game transacts too.
        val outsider = m.rpc.sendAsync(anvil.accounts[5], m.contract, "0x1234")
        m.watcher.observe()
        m.watcher.recorded.none { it.hash == outsider } shouldBe true

        // Submitting the outsider's transaction directly, during the audit, is rejected.
        m.session.settle()
        val tx = SignedTransaction.fromNode(m.rpc.txByHash(outsider))!!
        val rejection = runCatching { JsonRpc(anvil.rpcUrl).ethCall(anvil.accounts[0], m.contract, m.watcher.evidenceCall(tx)) }
        rejection.exceptionOrNull()!!.message!! shouldContain "not an audited account"

        val (outcomes, payoffs) = m.finish()
        outcomes.single { it.tx.hash == replay }.reason shouldContain "with an earlier transaction for its node"
        outcomes.filter { it.charged }.map { it.tx.hash } shouldBe listOf(replay)
        payoffs shouldBe mapOf(alice to 4L, bob to 16L - bobsDeposit)
    }

    test("a fee bump is the same transaction, not a second one") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, false); m.play(bob, false)
        m.play(alice, false)
        // Bob opens in his phase, then bumps the fee of the pending opening: same nonce and calldata.
        m.quit(bob)
        m.rpc.setAutomine(false)
        val calldata = m.openingCalldata(bob)
        val nonce = m.rpc.nonce(m.account(bob))
        val first = m.rpc.sendAsync(m.account(bob), m.contract, calldata, nonce = nonce)
        m.watcher.observe()
        val price = m.rpc.txByHash(first)["gasPrice"]!!.jsonPrimitive.content.removePrefix("0x").toLong(16)
        val bumped = m.rpc.sendAsync(m.account(bob), m.contract, calldata, nonce = nonce, gasPrice = 2 * price + 1)
        m.watcher.observe()
        m.rpc.setAutomine(true)
        m.rpc.evmMine()
        m.rpc.receiptStatus(bumped) shouldBe true
        m.watcher.recorded.map { it.hash }.containsAll(listOf(first, bumped)) shouldBe true

        val (outcomes, _) = m.finish()
        outcomes.single { it.tx.hash == bumped }.charged shouldBe false
        outcomes.filter { it.charged }.shouldBeEmpty()
    }

    test("an opening made in its phase is not evidence, even when it is included after the deadline") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, false); m.play(bob, false)
        m.play(alice, false)
        // Bob signs his opening once it is his turn, but it lands after his deadline and reverts.
        m.quit(bob)
        val calldata = m.openingCalldata(bob)
        m.rpc.advanceTime(vegas.backend.evm.EvmConstants.TIMEOUT_SECONDS.toLong() + 1)
        val late = m.rpc.sendAsync(m.account(bob), m.contract, calldata)
        m.rpc.receiptStatus(late) shouldBe false
        m.watcher.observe()

        val (outcomes, payoffs) = m.finish()
        outcomes.single { it.tx.hash == late }.reason shouldContain "well-formed move"
        outcomes.filter { it.charged }.shouldBeEmpty()
        payoffs shouldBe m.session.modelPayoffs().mapValues { it.value.toLong() }
    }

    test("quitting is never charged: neither letting one's own commitment expire nor withholding an opening") {
        val missed = start()
        missed.play(alice); missed.play(bob)
        missed.play(alice, true)
        missed.quit(bob)
        missed.play(alice, true)
        missed.quit(bob) // the model's record of Bob's persistent quit at his opening
        // Bob quit, so he gets his exit payout (0); Alice gets the split pot.
        missed.finish().second shouldBe missed.session.modelPayoffs().mapValues { it.value.toLong() }
        missed.charged(bob) shouldBe false
        missed.charged(alice) shouldBe false
        anvil.stop(); anvil.start()

        val withheld = start()
        withheld.play(alice); withheld.play(bob)
        withheld.play(alice, true); withheld.play(bob, true)
        withheld.quit(alice)
        withheld.play(bob, true)
        withheld.finish().second shouldBe withheld.session.modelPayoffs().mapValues { it.value.toLong() }
        withheld.charged(alice) shouldBe false
        withheld.charged(bob) shouldBe false
    }

    test("a transaction that is not a well-formed move is evidence: a wrong opening, extra bytes, a call to settle") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, false); m.play(bob, false)
        // In her own phase, Alice sends an opening that does not open her commitment.
        val wrong = m.rpc.sendAsync(m.account(alice), m.contract, m.openingCalldata(alice, salt = 12345))
        m.rpc.receiptStatus(wrong) shouldBe false
        // Bob re-sends his commitment call with bytes appended: a covert channel.
        val bobsCommit = m.watcher.recorded.last { it.from == m.account(bob).lowercase() }
        val padded = m.rpc.sendAsync(m.account(bob), m.contract,
            m.rpc.txByHash(bobsCommit.hash)["input"]!!.jsonPrimitive.content + "00".repeat(32))
        // Bob also calls settle(): not a move, so its timing could signal. Anyone outside the game may call it.
        val settle = m.rpc.sendAsync(m.account(bob), m.contract, Hex.encode(AbiCodec.functionSelector("settle()")))
        m.watcher.observe()
        m.play(alice, false); m.play(bob, false)

        val (outcomes, payoffs) = m.finish()
        outcomes.single { it.tx.hash == wrong }.charged shouldBe true
        outcomes.single { it.tx.hash == padded }.charged shouldBe true
        outcomes.single { it.tx.hash == settle }.charged shouldBe true
        payoffs shouldBe mapOf(alice to 4L - deposit, bob to 16L - bobsDeposit)
    }

    test("events become ready one at a time: Bob's commitment is ready only once Alice's is resolved") {
        val m = start()
        m.play(alice); m.play(bob)
        m.session.settle()
        m.session.readyAt(evm.schedule.indexOf(m.commitNode(alice))) shouldBeGreaterThan 0L
        m.session.readyAt(evm.schedule.indexOf(m.commitNode(bob))) shouldBe 0L
        m.play(alice, true)
        m.session.readyAt(evm.schedule.indexOf(m.commitNode(bob))) shouldBeGreaterThan 0L
    }

    test("the watch command audits a finished game") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, true)
        val leak = m.rpc.sendAsync(m.account(alice), m.contract, m.earlyRevealCalldata())
        m.play(bob, true)
        m.play(alice, true); m.play(bob, true)
        m.session.settle()
        // The command polls from the start of the chain, so it sees the whole game.
        val output = java.io.ByteArrayOutputStream()
        val stdout = System.out
        System.setOut(java.io.PrintStream(output, true))
        try {
            vegas.runWatcher(java.nio.file.Path.of("examples/Coordination.vg"), listOf(
                "--rpc", anvil.rpcUrl, "--contract", m.contract, "--reporter", anvil.accounts[0]))
        } finally {
            System.setOut(stdout)
        }
        val lines = output.toString().lines()
        lines.single { leak in it } shouldContain "Alice: CHARGED"
        // One report burns Alice's deposit; her later opening is a second transaction for its node, already paid for.
        lines.filter { "reported" in it } shouldHaveSize 1
    }

    test("moves carry the hash of their readiness block as credential, so an early move cannot be replayed later") {
        val m = start()
        m.play(alice); m.play(bob)
        m.play(alice, true)
        val leak = m.rpc.sendAsync(m.account(alice), m.contract, m.earlyRevealCalldata())
        m.rpc.receiptStatus(leak) shouldBe false
        m.play(bob, true)
        // Once it is Alice's turn, the same signed call is still rejected: its credential predates readiness.
        val again = m.rpc.sendAsync(m.account(alice), m.contract, m.rpc.txByHash(leak)["input"]!!.jsonPrimitive.content)
        m.rpc.receiptStatus(again) shouldBe false
        m.play(alice, true)
        m.watcher.observe()
        // join, commit, the early call, its later copy, and the real reveal
        m.watcher.recorded.filter { it.from == m.account(alice).lowercase() } shouldHaveSize 5
    }
})

package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.ir.Expr
import vegas.semantics.Configuration
import vegas.semantics.GameSemantics
import vegas.semantics.Label
import vegas.semantics.PlayTag
import vegas.semantics.reconstructViews

/** A semantic probe, not a proof of the Kotlin-to-Lean translation. */
class OptionalDisclosureTest : FreeSpec({
    val alice = RoleId("Alice")
    val bob = RoleId("Bob")
    val coin = RoleId("Coin")
    val secret = FieldRef(alice, VarId("secret"))
    val signal = FieldRef(coin, VarId("signal"))

    val source = requireNotNull(javaClass.getResource("/optional-disclosure.vg")).readText()
    val ast = parseCode(source)
    typeCheck(ast)
    val ir = compileToIR(ast)
    val semantics = GameSemantics(ir)

    fun advance(config: Configuration, move: Label): Configuration = when (move) {
        is Label.Play -> config.copy(
            partialFrontierAssignment = config.partialFrontierAssignment + move.delta
        )
        is Label.FinalizeFrontier -> Configuration(
            config.frontier.resolveEnabled(),
            config.history with config.partialFrontierAssignment
        )
    }

    // Canonical role order avoids enumerating permutations of a simultaneous
    // frontier's partial assignments; values are not visible until finalization.
    fun configurations(config: Configuration): List<Configuration> {
        val moves = semantics.enabledMoves(config)
        val plays = moves.filterIsInstance<Label.Play>()
        val role = plays.firstOrNull()?.role
        val next = if (role == null) moves else plays.filter { it.role == role }
        return listOf(config) + next.flatMap { configurations(advance(config, it)) }
    }

    val checkpoints = configurations(Configuration.initial(ir)).filter { config ->
        config.partialFrontierAssignment.isEmpty() &&
            config.history.get(secret) is Expr.Const.Hidden &&
            semantics.enabledMoves(config).filterIsInstance<Label.Play>().any { move ->
                move.role == alice && move.delta[secret] is Expr.Const.BoolVal
            }
    }

    "disclosure is a later choice with exactly the original opening or quit" {
        checkpoints.shouldHaveSize(4)
        checkpoints.forEach { config ->
            val binding = config.history.get(secret) as Expr.Const.Hidden
            val moves = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
                .filter { it.role == alice }
            moves.filter { it.tag is PlayTag.Action }.map { it.delta[secret] } shouldBe
                listOf(binding.inner)
            moves.filter { it.tag is PlayTag.Quit }.map { it.delta[secret] } shouldBe
                listOf(Expr.Const.Quit)
            (config.history.get(signal) is Expr.Const.BoolVal) shouldBe true
            val views = reconstructViews(config.history, ir.roles + ir.chanceRoles)
            views.getValue(alice).get(secret) shouldBe binding.inner
            views.getValue(bob).get(secret) shouldBe Expr.Const.Opaque
            views.getValue(alice).get(signal) shouldBe config.history.get(signal)
        }
    }

    "quitting is public without revealing the original binding" {
        checkpoints.shouldHaveSize(4)
        checkpoints.forEach { config ->
            val quit = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
                .single { it.role == alice && it.tag is PlayTag.Quit }
            val pending = advance(config, quit)
            semantics.enabledMoves(pending).contains(Label.FinalizeFrontier) shouldBe true
            val resolved = advance(pending, Label.FinalizeFrontier)
            val view = reconstructViews(resolved.history, ir.roles + ir.chanceRoles).getValue(bob)
            view.get(secret) shouldBe Expr.Const.Quit
            view.past!!.get(secret) shouldBe Expr.Const.Opaque
        }
    }
})

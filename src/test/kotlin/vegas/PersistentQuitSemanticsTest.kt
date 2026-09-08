package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.ir.Expr
import vegas.semantics.Configuration
import vegas.semantics.GameSemantics
import vegas.semantics.Label
import vegas.semantics.PlayTag
import vegas.semantics.applyMove
import vegas.semantics.reconstructViews

class PersistentQuitSemanticsTest : FreeSpec({
    val source = """
        game main() {
          join Alice() ${'$'} 10 Bob() ${'$'} 10;
          commit Alice(secret: bool) || null;
          yield Alice(first: bool) || null;
          yield Bob(intervenes: bool) || null;
          yield Alice(second: bool) || null;
          reveal Alice(secret: bool) || null;
          withdraw (Alice.first == null || Alice.second == null || Alice.secret == null)
            ? { Bob -> 20 } : { Alice -> 20 }
        }
    """.trimIndent()

    val ast = parseCode(source)
    typeCheck(ast)
    val ir = compileToIR(ast)
    val semantics = GameSemantics(ir)
    val alice = RoleId("Alice")
    val bob = RoleId("Bob")
    val secret = FieldRef(alice, VarId("secret"))
    val first = FieldRef(alice, VarId("first"))
    val second = FieldRef(alice, VarId("second"))
    val intervenes = FieldRef(bob, VarId("intervenes"))

    fun finalize(config: Configuration): Configuration {
        semantics.canFinalizeFrontier(config) shouldBe true
        semantics.enabledMoves(config).contains(Label.FinalizeFrontier) shouldBe true
        return applyMove(config, Label.FinalizeFrontier)
    }

    fun action(config: Configuration, role: RoleId, field: FieldRef): Label.Play =
        semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .first { it.role == role && it.tag is PlayTag.Action && field in it.delta }

    fun advanceToFirstChoice(secretValue: Boolean): Configuration {
        var config = Configuration.initial(ir)
        config = finalize(config)
        val commit = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .first { move ->
                move.role == alice &&
                    (move.delta[secret] as? Expr.Const.Hidden)?.inner ==
                    Expr.Const.BoolVal(secretValue)
            }
        config = finalize(applyMove(config, commit))
        return config
    }

    "quitting once removes later owner actions but preserves the opaque commitment" {
        var config = advanceToFirstChoice(true)
        val quit = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .single { it.role == alice && it.tag is PlayTag.Quit }
        config = finalize(applyMove(config, quit))

        val bobMove = action(config, bob, intervenes)
        config = finalize(applyMove(config, bobMove))

        val laterOwnerMoves = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .filter { it.role == alice }
        laterOwnerMoves.filter { it.tag is PlayTag.Action }.shouldBeEmpty()
        laterOwnerMoves.isNotEmpty() shouldBe true
        laterOwnerMoves.all { it.tag is PlayTag.Quit } shouldBe true
        config = finalize(config)
        val revealOwnerMoves = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .filter { it.role == alice }
        revealOwnerMoves.filter { it.tag is PlayTag.Action }.shouldBeEmpty()
        revealOwnerMoves.isNotEmpty() shouldBe true
        revealOwnerMoves.all { it.tag is PlayTag.Quit } shouldBe true
        config = finalize(config)

        config.isTerminal() shouldBe true
        semantics.enabledMoves(config).shouldBeEmpty()

        val bobView = reconstructViews(config.history, ir.roles).getValue(bob)
        bobView.get(secret) shouldBe Expr.Const.Opaque
        bobView.get(first) shouldBe Expr.Const.Quit
    }

    "not quitting leaves the later owner choice enabled" {
        var config = advanceToFirstChoice(false)
        config = finalize(applyMove(config, action(config, alice, first)))
        config = finalize(applyMove(config, action(config, bob, intervenes)))

        val later = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
            .filter { it.role == alice && it.tag is PlayTag.Action }
        later.any { second in it.delta } shouldBe true
    }
})

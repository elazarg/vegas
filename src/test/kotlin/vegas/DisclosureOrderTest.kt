package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.shouldBe
import vegas.frontend.compileToIR
import vegas.frontend.inlineMacros
import vegas.frontend.parseCode
import vegas.golden.parseExample
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.Visibility
import vegas.semantics.Configuration
import vegas.semantics.GameSemantics
import vegas.semantics.Label
import vegas.semantics.PlayTag
import vegas.semantics.applyMove
import vegas.semantics.reconstructViews

/**
 * Openings are public events and happen one at a time, in source order, as
 * they do on an asynchronous ledger: a later revealer sees the earlier
 * openings before choosing whether to open. Joining is a precondition of the
 * game, not a move, so it cannot be quit.
 */
class DisclosureOrderTest : FreeSpec({

    /** Play the first available action of every role until the game ends, recording each frontier. */
    fun frontiers(ir: GameIR): List<Set<Pair<String, Visibility>>> {
        val semantics = GameSemantics(ir)
        var config = Configuration.initial(ir)
        val seen = mutableListOf<Set<Pair<String, Visibility>>>()
        while (!config.isTerminal()) {
            seen += config.enabled().map { it.first.name to ir.dag.kind(it) }.toSet()
            while (true) {
                val play = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
                    .firstOrNull { it.tag is PlayTag.Action } ?: break
                config = applyMove(config, play)
            }
            config = applyMove(config, Label.FinalizeFrontier)
        }
        return seen
    }

    fun revealFrontiers(ir: GameIR) = frontiers(ir).filter { f -> f.any { it.second == Visibility.REVEAL } }

    "simultaneous public choices are committed together and opened in declaration order" {
        val ir = compileToIR(inlineMacros(parseExample("RandomLeader")))
        frontiers(ir).first { f -> f.any { it.second == Visibility.COMMIT } } shouldBe
            setOf("V1" to Visibility.COMMIT, "V2" to Visibility.COMMIT, "V3" to Visibility.COMMIT)
        revealFrontiers(ir) shouldBe listOf(
            setOf("V1" to Visibility.REVEAL),
            setOf("V2" to Visibility.REVEAL),
            setOf("V3" to Visibility.REVEAL),
        )
    }

    "an explicit multi-role reveal opens in the order written" {
        val ir = compileToIR(inlineMacros(parseExample("RPSLS")))
        revealFrontiers(ir) shouldBe listOf(setOf("P1" to Visibility.REVEAL), setOf("P2" to Visibility.REVEAL))
    }

    "the later revealer decides with the earlier opening in view" {
        val ir = compileToIR(inlineMacros(parseExample("Prisoners")))
        val semantics = GameSemantics(ir)
        val a = RoleId("A")
        val b = RoleId("B")
        val aChoice = FieldRef(a, VarId("c"))
        var config = Configuration.initial(ir)
        while (config.enabled().none { ir.dag.owner(it) == b && ir.dag.kind(it) == Visibility.REVEAL }) {
            while (true) {
                val play = semantics.enabledMoves(config).filterIsInstance<Label.Play>()
                    .firstOrNull { it.tag is PlayTag.Action } ?: break
                config = applyMove(config, play)
            }
            config = applyMove(config, Label.FinalizeFrontier)
        }
        val bView = reconstructViews(config.history, ir.roles).getValue(b)
        (bView.get(aChoice) is Expr.Const.BoolVal) shouldBe true
    }

    "a join offers no quit, even with parameters" {
        val ir = compileToIR(inlineMacros(parseCode("""
            game main() {
              join A(x: bool) ${'$'} 10;
              join B(y: bool) ${'$'} 10;
              withdraw (A.x <-> B.y) ? { A -> 20; B -> 0 } : { A -> 0; B -> 20 }
            }
        """.trimIndent())))
        val semantics = GameSemantics(ir)
        semantics.enabledMoves(Configuration.initial(ir)).filterIsInstance<Label.Play>()
            .filter { it.tag is PlayTag.Quit }.shouldBeEmpty()
    }
})

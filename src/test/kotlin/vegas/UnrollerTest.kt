package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf
import vegas.backend.gambit.*
import vegas.dag.FrontierMachine
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.ir.Expr
import vegas.semantics.Configuration
import vegas.semantics.GameSemantics
import vegas.semantics.History

/**
 * Test suite for TreeUnroller.
 *
 * Tests that TreeUnroller correctly converts LTS semantics into GameTree structures.
 * These are standalone tests that validate TreeUnroller behavior independently
 * before comparing with the existing implementation.
 */
class UnrollerTest : FreeSpec({

    fun compileGame(code: String) = compileToIR(parseCode(code))

    "TreeUnroller" - {

        "produces terminal node for trivial game" {
            val code = """
                join Alice() $ 100;
                withdraw { Alice -> 100 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)

            // Should be terminal since join has no parameters
            tree.shouldBeInstanceOf<GameTree.Terminal>()
            tree.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(0)
        }

        "handles single-role simple game with choice" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> (Alice.x ? 10 : 5) }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)

            // Should have Alice's decision node (x: bool)
            tree.shouldBeInstanceOf<GameTree.Decision>()
            tree.owner shouldBe RoleId("Alice")
            tree.isChance shouldBe false

            // Should have 3 choices: true, false, quit
            tree.choices.shouldHaveSize(3)

            // All subtrees should be terminal with correct payoffs
            val trueChoice = tree.choices[0]
            trueChoice.subtree.shouldBeInstanceOf<GameTree.Terminal>()
            (trueChoice.subtree as GameTree.Terminal).payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-90)

            val falseChoice = tree.choices[1]
            falseChoice.subtree.shouldBeInstanceOf<GameTree.Terminal>()
            (falseChoice.subtree as GameTree.Terminal).payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-95)

            val quitChoice = tree.choices[2]
            quitChoice.subtree.shouldBeInstanceOf<GameTree.Terminal>()
        }

        "creates continuation nodes with FAIR_PLAY policy" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> (Alice.x ? 10 : 5) }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            // FAIR_PLAY policy should expand explicit actions but defer quit
            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)

            tree.shouldBeInstanceOf<GameTree.Decision>()

            // Should have 3 choices: true (expanded), false (expanded), quit (continuation)
            tree.choices.shouldHaveSize(3)

            // True and false should be expanded to terminals
            tree.choices[0].subtree.shouldBeInstanceOf<GameTree.Terminal>()
            tree.choices[1].subtree.shouldBeInstanceOf<GameTree.Terminal>()

            // Quit should be a continuation
            tree.choices[2].subtree.shouldBeInstanceOf<GameTree.Continuation>()
        }

        "correctly computes payoffs at terminals" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(bet: bool);
                yield Bob(call: bool);
                withdraw (Alice.bet && Bob.call)
                    ? { Alice -> 20; Bob -> 0 }
                    : (Alice.bet && !Bob.call)
                    ? { Alice -> 5; Bob -> 15 }
                    : (!Alice.bet && Bob.call)
                    ? { Alice -> 15; Bob -> 5 }
                    : { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)

            // Navigate to Alice bets true, Bob calls true
            tree.shouldBeInstanceOf<GameTree.Decision>()
            val aliceBetsTrue = tree.choices[0].subtree as GameTree.Decision
            val bobCallsTrue = aliceBetsTrue.choices[0].subtree as GameTree.Terminal

            bobCallsTrue.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-80)
            bobCallsTrue.payoffs[RoleId("Bob")] shouldBe Expr.Const.IntVal(-100)

            // Navigate to Alice bets true, Bob calls false
            val bobCallsFalse = aliceBetsTrue.choices[1].subtree as GameTree.Terminal
            bobCallsFalse.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-95)
            bobCallsFalse.payoffs[RoleId("Bob")] shouldBe Expr.Const.IntVal(-85)

            // Navigate to Alice bets false, Bob calls true
            val aliceBetsFalse = tree.choices[1].subtree as GameTree.Decision
            val bobCallsTrue2 = aliceBetsFalse.choices[0].subtree as GameTree.Terminal
            bobCallsTrue2.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-85)
            bobCallsTrue2.payoffs[RoleId("Bob")] shouldBe Expr.Const.IntVal(-95)

            // Navigate to Alice bets false, Bob calls false
            val bobCallsFalse2 = aliceBetsFalse.choices[1].subtree as GameTree.Terminal
            bobCallsFalse2.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-90)
            bobCallsFalse2.payoffs[RoleId("Bob")] shouldBe Expr.Const.IntVal(-90)
        }

        "handles chance nodes correctly" {
            val code = """
                random Nature() $ 0;
                join Alice() $ 100;
                yield Nature(coin: bool);
                yield Alice(bet: bool);
                withdraw (Nature.coin == Alice.bet)
                    ? { Nature -> 0; Alice -> 10 }
                    : { Nature -> 0; Alice -> 0 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)

            // First decision should be Nature (chance)
            tree.shouldBeInstanceOf<GameTree.Decision>()
            tree.owner shouldBe RoleId("Nature")
            tree.isChance shouldBe true

            // Chance should have exactly 2 choices (no quit for chance)
            tree.choices.shouldHaveSize(2)

            // Each choice should have probability 1/2
            tree.choices[0].probability shouldBe Rational(1, 2)
            tree.choices[1].probability shouldBe Rational(1, 2)

            // Both branches should expand to Alice's decision (chance always expands)
            tree.choices[0].subtree.shouldBeInstanceOf<GameTree.Decision>()
            tree.choices[1].subtree.shouldBeInstanceOf<GameTree.Decision>()
        }

        "handles sequential actions for same role" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                yield Alice(y: bool);
                withdraw { Alice -> (Alice.x && Alice.y ? 20 : 10) }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            val tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)

            // First decision for x
            tree.shouldBeInstanceOf<GameTree.Decision>()
            tree.owner shouldBe RoleId("Alice")

            // After choosing x, should have another decision for y
            val afterX = tree.choices[0].subtree
            afterX.shouldBeInstanceOf<GameTree.Decision>()
            afterX.owner shouldBe RoleId("Alice")

            // Both x and y true should give payoff 20
            val terminal = afterX.choices[0].subtree as GameTree.Terminal
            terminal.payoffs[RoleId("Alice")] shouldBe Expr.Const.IntVal(-80)
        }

        "skeleton policy creates all continuations" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(x: bool);
                yield Bob(y: bool);
                withdraw { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ir = compileGame(code)
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)

            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )

            // SKELETON policy should defer all expansions
            val tree = unroller.unroll(initialConfig, ExpansionPolicy.SKELETON)

            tree.shouldBeInstanceOf<GameTree.Decision>()

            // All choices should be continuations
            tree.choices.forEach { choice ->
                choice.subtree.shouldBeInstanceOf<GameTree.Continuation>()
            }
        }
    }

    "TreeUnroller vs Existing Implementation" - {

        "produces identical EFG for simple games" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> (Alice.x ? 10 : 5) }
            """.trimIndent()

            val ir = compileGame(code)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = true)

            // New implementation via TreeUnroller
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for two-player games" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(bet: bool);
                yield Bob(call: bool);
                withdraw (Alice.bet && Bob.call)
                    ? { Alice -> 20; Bob -> 0 }
                    : { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ir = compileGame(code)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = true)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FULL_EXPANSION)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG with FAIR_PLAY policy" {
            val code = """
                join Alice() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> (Alice.x ? 10 : 5) }
            """.trimIndent()

            val ir = compileGame(code)

            // Old implementation with FAIR_PLAY
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation with FAIR_PLAY
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for chance games" {
            val code = """
                random Nature() $ 0;
                join Alice() $ 100;
                yield Nature(coin: bool);
                yield Alice(bet: bool);
                withdraw (Nature.coin == Alice.bet)
                    ? { Nature -> 0; Alice -> 10 }
                    : { Nature -> 0; Alice -> 0 }
            """.trimIndent()

            val ir = compileGame(code)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for commit-reveal games" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                commit Alice(secret: bool);
                yield Bob(guess: bool);
                withdraw (Alice.secret == Bob.guess)
                    ? { Alice -> 0; Bob -> 20 }
                    : { Alice -> 20; Bob -> 0 }
            """.trimIndent()

            val ir = compileGame(code)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }
    }

    "TreeUnroller on Example Files" - {

        fun loadExample(name: String): String {
            return java.io.File("examples/$name.vg").readText()
        }

        "produces identical EFG for Trivial1" {
            val code = loadExample("Trivial1")
            val ast = parseCode(code)
            val ir = compileToIR(ast)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for Simple" {
            val code = loadExample("Simple")
            val ast = parseCode(code)
            val ir = compileToIR(ast)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for OddsEvensShort" {
            val code = loadExample("OddsEvensShort")
            val ast = parseCode(code)
            val ir = compileToIR(ast)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }

        "produces identical EFG for MontyHallChance" {
            val code = loadExample("MontyHallChance")
            val ast = parseCode(code)
            val ir = compileToIR(ast)

            // Old implementation
            val oldEfg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // New implementation
            val semantics = GameSemantics(ir)
            val unroller = TreeUnroller(semantics, ir)
            val initialConfig = Configuration(
                frontier = FrontierMachine.from(ir.dag),
                history = History(),
                partialFrontierAssignment = emptyMap()
            )
            var tree = unroller.unroll(initialConfig, ExpansionPolicy.FAIR_PLAY)
            tree = pruneContinuations(tree)
            val newEfg = ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            newEfg shouldBe oldEfg
        }
    }
})

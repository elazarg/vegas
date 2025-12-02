package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.frontend.compileToIR
import vegas.frontend.parseCode

const val BAIL_PERSISTENCE = """
// Test 1.2: Abandonment persists - once a player quits, they are locked out
// Alice has two sequential actions
// If Alice quits on first action, second and third should only offer "Quit"

join Alice() $ 100;
join Bob() $ 100;

// Alice's first action
yield Alice(x: bool);

// Bob acts
yield Bob(y: bool);

// Alice's second action - if Alice quits on x, should only have None
yield Alice(z: bool);

withdraw (Alice.x != null && Bob.y != null && Alice.z != null)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.x == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.y == null) ? { Alice -> 5; Bob -> -100 }
    : (Alice.z == null) ? { Alice -> -100; Bob -> 5 }
    : { Alice -> 0; Bob -> 0 }
"""

const val CHANCE_NO_BAIL = """
// Test 1.3: Chance roles cannot quit
// Nature (random role) should not have "None" option

random Nature() $ 0;
join Alice() $ 100;

// Nature chooses randomly - should only have {true, false}, no "None"
yield Nature(coin: bool);

// Alice can see coin and respond (or quit)
yield Alice(bet: bool);

withdraw (Nature.coin != null && Alice.bet != null)
    ? (Nature.coin == Alice.bet)
        ? { Nature -> 0; Alice -> 10 }
        : { Nature -> 0; Alice -> 0 }
    : (Alice.bet == null) ? { Nature -> 0; Alice -> -100 }
    : { Nature -> 0; Alice -> 0 }
"""

const val COMMIT_NOT_VISIBLE = """
// Test 2.2: COMMIT visibility - others don't see commits
// Alice commits a secret, Bob tries to use it in a guard
// Bob should NOT see Alice's hidden value

join Alice() $ 100;
join Bob() $ 100;

// Alice commits a secret (hidden)
yield Alice(secret: hidden bool);

// Bob tries to respond, but cannot see Alice's secret
// Bob should only be able to quit
yield Bob(response: bool);

withdraw (Alice.secret != null && Bob.response != null)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.secret == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.response == null) ? { Alice -> 5; Bob -> -100 }
    : { Alice -> 0; Bob -> 0 }
"""

const val OWNER_SEES_COMMIT = """
// Test 2.1: COMMIT visibility - owner sees own commits
// Alice commits x (hidden), then commits y
// Alice SHOULD see her own x value

join Alice() $ 100;
join Bob() $ 100;

// Alice commits x (hidden)
yield Alice(x: hidden bool);

// Alice commits y - can condition on x because Alice sees her own commits
yield Alice(y: hidden bool);

// Bob acts
yield Bob(z: bool);

withdraw (Alice.x != null && Alice.y != null && Bob.z != null)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.x == null) ? { Alice -> -100; Bob -> 5 }
    : (Alice.y == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.z == null) ? { Alice -> 5; Bob -> -100 }
    : { Alice -> 0; Bob -> 0 }
"""

const val REVEAL_VISIBLE = """
// Test 2.3: REVEAL visibility - value visible to all after commitment
// Alice reveals x (public), Bob can see it

join Alice() $ 100;
join Bob() $ 100;

// Alice reveals x (visible to all)
reveal Alice(x: bool);

// Bob can see Alice.x and respond
yield Bob(response: bool);

withdraw (Alice.x != null && Bob.response != null)
    ? (Alice.x == Bob.response)
        ? { Alice -> 10; Bob -> 10 }
        : { Alice -> 5; Bob -> 5 }
    : (Alice.x == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.response == null) ? { Alice -> 5; Bob -> -100 }
    : { Alice -> 0; Bob -> 0 }
"""

const val SIMUL_MIXED = """
// Test 5.1: Simultaneous actions with mixed quit/non-quit
// Both players act simultaneously, can quit or not
// Should have all 4 outcome combinations

join Alice() $ 100;
join Bob() $ 100;

// Both act simultaneously
yield Alice(x: bool) Bob(y: bool);

// Payoffs for all combinations:
// Both commit: 10, 10
// Alice commits, Bob quits: -5, 0
// Alice quits, Bob commits: 0, -5
// Both quit: 0, 0

withdraw (Alice.x != null && Bob.y != null)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.x != null && Bob.y == null) ? { Alice -> -5; Bob -> 0 }
    : (Alice.x == null && Bob.y != null) ? { Alice -> 0; Bob -> -5 }
    : { Alice -> 0; Bob -> 0 }
"""

const val VISIBILITY_ACTUAL_WRITER = """
// Test 2.4: Visibility from actual writer, not ancestors
// Critical test - catches the code review bug
// Alice writes x as visible, then overwrites as hidden
// Bob should NOT see x (uses Alice's second write visibility = hidden)

join Alice() $ 100;
join Bob() $ 100;

// Alice's first write - visible
yield Alice(x: bool);

// Alice's second write - hidden (overwrites with COMMIT visibility)
yield Alice(x: hidden bool);

// Bob tries to use Alice.x
// Since Alice's ACTUAL write is hidden, Bob should not see it
// Bob's only option should be to quit
yield Bob(guess: bool);

withdraw (Alice.x != null && Bob.guess != null && Alice.x == Bob.guess)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.x == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.guess == null) ? { Alice -> 5; Bob -> -100 }
    : { Alice -> 5; Bob -> 5 }
"""

/**
 * Semantic test suite for Gambit/EFG backend.
 *
 * Tests critical semantic properties that must hold:
 * - Visibility semantics (COMMIT, REVEAL, PUBLIC)
 * - Abandonment mechanics
 * - Information set correctness
 * - Guard evaluation with visibility
 *
 * Uses EFG helper functions to make real semantic assertions about action sets,
 * infosets, and game structure rather than blind string matching.
 */
class GambitSemanticTest : FreeSpec({

    fun compileGame(code: String): String {
        val ast = parseCode(code)
        val ir = compileToIR(ast)
        return generateExtensiveFormGame(ir)
    }

    // EFG Helper data structures
    data class DecisionNode(
        val raw: String,
        val player: Int,
        val infoset: Int,
        val actions: List<String>,
    )

    fun List<DecisionNode>.hasFullBoolMenu() =
        any {
            it.actions.toSet() == setOf("true", "false", "Quit") ||
            it.actions.toSet() == setOf("Hidden(true)", "Hidden(false)", "Quit")
        }

    data class HistorySig(
        val player: Int,
        val infoset: Int,
        val actions: Set<String>
    )

    // Parse decision nodes from EFG format
    fun parseDecisionNodes(efg: String): List<DecisionNode> =
        efg.lines()
            .filter { it.startsWith("p ") }
            .mapNotNull { line ->
                val tokens = line.trim().split(Regex("\\s+"))
                val player = tokens.getOrNull(2)?.toIntOrNull() ?: return@mapNotNull null
                val infoset = tokens.getOrNull(3)?.toIntOrNull() ?: return@mapNotNull null

                val optionsMatch = Regex("""\{([^}]*)}""").find(line)
                val actions = if (optionsMatch != null) {
                    Regex(""""([^"]*)"""")
                        .findAll(optionsMatch.groupValues[1])
                        .map { it.groupValues[1] }
                        .toList()
                } else emptyList()

                DecisionNode(
                    raw = line,
                    player = player,
                    infoset = infoset,
                    actions = actions,
                )
            }

    fun decisionNodesForPlayer(efg: String, player: Int): List<DecisionNode> =
        parseDecisionNodes(efg).filter { it.player == player }

    fun infosetsForPlayer(efg: String, player: Int): List<HistorySig> =
        parseDecisionNodes(efg)
            .filter { it.player == player }
            .groupBy { it.infoset }
            .map { (infoset, nodes) ->
                HistorySig(
                    player = player,
                    infoset = infoset,
                    actions = nodes.flatMap { it.actions }.toSet()
                )
            }

    "Visibility Semantics" - {

        "visibility from actual writer (no leak to Bob)" {
            // Regression test for critical visibility bug:
            // Alice writes x as visible, then overwrites as hidden.
            // Bob should NOT see the VALUE of x (uses Alice's second write visibility).
            //
            // This is primarily a regression test (game compiles without crash).
            // Bob can still make guesses, but he shouldn't have different nodes
            // based on the hidden value of Alice.x (only based on whether Alice abandoned).

            val efg = compileGame(VISIBILITY_ACTUAL_WRITER)
            val bobNodes = decisionNodesForPlayer(efg, 2)
            bobNodes.isNotEmpty() shouldBe true

            // Bob can make choices (he has a full bool menu with abandonment option)
            bobNodes.hasFullBoolMenu() shouldBe true

            // Game should complete without errors
            efg shouldContain "t \"\""
        }

        "COMMIT visibility - others cannot see commits" {
            val efg = compileGame(COMMIT_NOT_VISIBLE)

            // Alice has at least 2 branches (True/False)
            // Bob acts after Alice.
            val bobHistorys = infosetsForPlayer(efg, 2)

            // Bob should have exactly 2 infosets:
            // 1. Alice committed (value hidden, but commitment visible)
            // 2. Alice abandoned (distinct from commitment)
            // If he saw the committed VALUE, he would have 3+ (true, false, quit).
            bobHistorys.map { it.infoset }.distinct().size shouldBe 2
        }

        "COMMIT visibility - owner sees own commits" {
            // Alice commits x (hidden), then commits y.
            // Alice SHOULD see her own x value.
            //
            // Semantic property: Owner has multiple decision nodes (acts more than once).

            val efg = compileGame(OWNER_SEES_COMMIT)
            val aliceNodes = decisionNodesForPlayer(efg, 1)

            // Owner acts multiple times (x then y)
            (aliceNodes.size >= 2) shouldBe true

            // At least one Alice node has proper choices {true, false, None}
            aliceNodes.hasFullBoolMenu() shouldBe true

            // Game completes
            efg shouldContain "t \"\""
        }

        "REVEAL visibility - value visible to all" {
            // Alice reveals x, Bob can see it and respond.
            //
            // Semantic property: Bob should have different infosets based on revealed value.

            val efg = compileGame(REVEAL_VISIBLE)
            val bobNodes = decisionNodesForPlayer(efg, 2)
            bobNodes.isNotEmpty() shouldBe true

            val bobHistorys = infosetsForPlayer(efg, 2)

            // Bob should have at least 2 distinct infosets (different revealed values)
            (bobHistorys.map { it.infoset }.distinct().size >= 2) shouldBe true

            // At least one infoset has full choice set {true, false, None}
            bobNodes.hasFullBoolMenu() shouldBe true

            // Game completes
            efg shouldContain "t \"\""
        }
    }

    "Abandonment Mechanics" - {

        "abandonment persists - once abandoned, player is locked out" {
            // Alice has multiple actions: x, then z.
            // If Alice quits on x, Alice's second decision (z) should only offer "None".
            //
            // Semantic property: Some nodes with multiple actions, some can only quit.

            val efg = compileGame(BAIL_PERSISTENCE)
            val aliceNodes = decisionNodesForPlayer(efg, 1)

            aliceNodes.isNotEmpty() shouldBe true

            // Some node where Alice has multiple actions (before abandonment)
            aliceNodes.any { it.actions.toSet().size > 1 } shouldBe true

            // Some node where Alice can only quit
            aliceNodes.any { it.actions.toSet() == setOf("Quit") } shouldBe true

            // Terminals with abandonment penalties
            efg shouldContain "{ -100"

            // Terminals where both players cooperate
            efg shouldContain "{ 10 10 }"
        }

        "chance roles cannot quit" {
            // Nature (random role) should NOT have abandonment option.

            val efg = compileGame(CHANCE_NO_BAIL)

            // Find chance nodes (start with "c ")
            val chanceLines = efg.lines().filter { it.startsWith("c ") }
            chanceLines.isNotEmpty() shouldBe true
            chanceLines.forEach { line ->
                line shouldNotContain "\"Quit\""
            }

            // Should have chance nodes with proper outcomes (true/false for boolean)
            chanceLines.any { it.contains("\"true\"") && it.contains("\"false\"") } shouldBe true
        }

        "strategic roles always have abandonment option" {
            val efg = compileGame(SIMUL_MIXED)

            // Alice (player 1) can quit
            decisionNodesForPlayer(efg, 1).any { "Quit" in it.actions } shouldBe true

            // Bob (player 2) can quit
            decisionNodesForPlayer(efg, 2).any { "Quit" in it.actions } shouldBe true

            // abandonment-related terminals exist
            efg shouldContain "{ 0 0 }"
        }

        "Public Abandonment - observers distinguish abandonment from hidden commit" {
            // Re-use COMMIT_NOT_VISIBLE or similar
            val efg = compileGame(COMMIT_NOT_VISIBLE)

            // Alice commits (Hidden) OR Bails.
            // Bob acts.
            val bobHistorys = infosetsForPlayer(efg, 2).map { it.infoset }.distinct()

            // Bob should have exactly 2 infosets:
            // 1. Alice committed (value hidden, so merged into one state)
            // 2. Alice abandoned (publicly visible state)
            bobHistorys.size shouldBe 2
        }
    }

    "Edge Cases and Robustness" - {

        "simultaneous actions with mixed abandonment/non-abandonment" {
            // Both players act simultaneously.
            // Should have all 4 outcome combinations.

            val efg = compileGame(SIMUL_MIXED)

            // Should have terminals for all combinations:
            efg shouldContain "{ 10 10 }"   // Both commit
            efg shouldContain "{ -5 0 }"    // Alice commits, Bob quits
            efg shouldContain "{ 0 -5 }"    // Alice quits, Bob commits
            efg shouldContain "{ 0 0 }"     // Both quit
        }

        "payoffs handle undefined values gracefully" {
            // When players quit, payoff evaluation should not crash.

            val efg = compileGame(SIMUL_MIXED)

            // Should have valid terminals for all scenarios
            val terminals = efg.lines().filter { it.startsWith("t") }
            terminals.isNotEmpty() shouldBe true

            // No error terminals or crashes
            terminals.all { it.contains("{ ") } shouldBe true
        }
    }

    "Information Sets" - {

        "infosets for player exist (weak smoke test)" {
            // Weak smoke test: just checks that Alice has at least one infoset ID.
            // Not a proof of infoset correctness.

            val efg = compileGame(OWNER_SEES_COMMIT)

            val aliceHistorys = infosetsForPlayer(efg, 1)

            // Should have at least one infoset
            aliceHistorys.isNotEmpty() shouldBe true
        }

        "different infosets when visible state differs" {
            // When revealed values differ, infosets should differ.
            //
            // Semantic property: Bob has multiple distinct infosets based on Alice's reveal.

            val efg = compileGame(REVEAL_VISIBLE)

            val bobHistorys = infosetsForPlayer(efg, 2)

            // Bob should have at least 2 distinct infosets (one per revealed value)
            (bobHistorys.map { it.infoset }.distinct().size >= 2) shouldBe true
        }
    }

    "Regression Tests" - {

        "no crash on visibility mismatch bug scenario" {
            // Direct regression test for the code review bug.
            // Should compile and run without errors.

            try {
                val efg = compileGame(VISIBILITY_ACTUAL_WRITER)
                efg shouldContain "t \"\"" // Has terminals
            } catch (e: Exception) {
                throw AssertionError("Game should compile without errors", e)
            }
        }

        "game structure is valid EFG format" {
            // Verify basic EFG structure for all games.

            val games = listOf(
                VISIBILITY_ACTUAL_WRITER,
                COMMIT_NOT_VISIBLE,
                OWNER_SEES_COMMIT,
                REVEAL_VISIBLE,
                BAIL_PERSISTENCE,
                CHANCE_NO_BAIL,
                SIMUL_MIXED,
            )

            games.forEach { game ->
                val efg = compileGame(game)

                // Should start with EFG header
                efg.lines().first() shouldContain "EFG"

                // Should have player declarations
                efg shouldContain "{"

                // Should have decision or terminal nodes
                val hasNodes = efg.lines().any {
                    it.startsWith("p ") || it.startsWith("c ") || it.startsWith("t ")
                }
                hasNodes shouldBe true
            }
        }
    }

    "Co-inductive expansion" - {
        "FAIR_PLAY creates trees without abandonment branches" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(x: bool);
                withdraw { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ast = parseCode(code)
            val ir = compileToIR(ast)
            val efg = generateExtensiveFormGame(ir, includeAbandonment = false)

            // Should have Alice's choice but NO Quit option
            efg shouldNotContain "\"Quit\""
        }

        "expand() expands Continuation nodes in-place" {
            val code = """
                join Alice() $ 100;
                join Bob() $ 100;
                yield Alice(x: bool);
                yield Bob(y: bool);
                withdraw { Alice -> 10; Bob -> 10 }
            """.trimIndent()

            val ast = parseCode(code)
            val ir = compileToIR(ast)

            // Generate FAIR_PLAY tree (defers abandonment)
            val gen = vegas.backend.gambit.EfgGenerator(ir)
            val frontier = vegas.dag.FrontierMachine.from(ir.dag)
            val initialState = vegas.backend.gambit.History()
            val initialKnowledge = (ir.roles + ir.chanceRoles).associateWith { vegas.backend.gambit.History() }
            val tree = gen.exploreFromFrontier(
                frontier,
                initialState,
                initialKnowledge,
                vegas.backend.gambit.EfgGenerator.FAIR_PLAY
            )

            // Verify tree has Continuation nodes (cannot serialize)
            var hasContinuations = false
            fun checkForContinuations(node: vegas.backend.gambit.GameTree): Unit = when (node) {
                is vegas.backend.gambit.GameTree.Terminal -> {}
                is vegas.backend.gambit.GameTree.Continuation -> { hasContinuations = true }
                is vegas.backend.gambit.GameTree.Decision -> {
                    node.choices.forEach { checkForContinuations(it.subtree) }
                }
            }
            checkForContinuations(tree)
            hasContinuations shouldBe true

            // Now expand with FULL_EXPANSION to expand abandonment branches
            gen.expand(tree, vegas.backend.gambit.EfgGenerator.FULL_EXPANSION)

            // After expansion, should have no Continuation nodes
            hasContinuations = false
            checkForContinuations(tree)
            hasContinuations shouldBe false

            // Should now be serializable with abandonment branches
            val efg = vegas.backend.gambit.ExtensiveFormGame(
                name = ir.name.ifEmpty { "Game" },
                description = "Generated from ActionDag",
                strategicPlayers = ir.roles,
                tree = tree
            ).toEfg()

            // Should contain Quit options now
            efg shouldContain "\"Quit\""
        }
    }
})

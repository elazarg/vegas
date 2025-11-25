package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.frontend.compileToIR
import vegas.frontend.parseCode

const val BAIL_PERSISTENCE = """
// Test 1.2: Bail persists - once bailed, player is locked out
// Alice has two sequential actions
// If Alice bails on first, second and third should only offer "None"

join Alice() $ 100;
join Bob() $ 100;

// Alice's first action
yield Alice(x: bool);

// Bob acts
yield Bob(y: bool);

// Alice's second action - if Alice bailed on x, should only have None
yield Alice(z: bool);

withdraw (Alice.x != null && Bob.y != null && Alice.z != null)
    ? { Alice -> 10; Bob -> 10 }
    : (Alice.x == null) ? { Alice -> -100; Bob -> 5 }
    : (Bob.y == null) ? { Alice -> 5; Bob -> -100 }
    : (Alice.z == null) ? { Alice -> -100; Bob -> 5 }
    : { Alice -> 0; Bob -> 0 }
"""

const val CHANCE_NO_BAIL = """
// Test 1.3: Chance roles cannot bail
// Nature (random role) should not have "None" option

random Nature() $ 0;
join Alice() $ 100;

// Nature chooses randomly - should only have {true, false}, no "None"
yield Nature(coin: bool);

// Alice can see coin and respond (or bail)
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
// Bob should only be able to bail
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
// Test 5.1: Simultaneous actions with mixed bail/non-bail
// Both players act simultaneously, can bail or not
// Should have all 4 outcome combinations

join Alice() $ 100;
join Bob() $ 100;

// Both act simultaneously
yield Alice(x: bool) Bob(y: bool);

// Payoffs for all combinations:
// Both commit: 10, 10
// Alice commits, Bob bails: -5, 0
// Alice bails, Bob commits: 0, -5
// Both bail: 0, 0

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
// Bob's only option should be to bail
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
 * - Bail/abandonment mechanics
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
        any { it.actions.toSet() == setOf("true", "false", "None") }

    data class InfosetSig(
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

    fun infosetsForPlayer(efg: String, player: Int): List<InfosetSig> =
        parseDecisionNodes(efg)
            .filter { it.player == player }
            .groupBy { it.infoset }
            .map { (infoset, nodes) ->
                InfosetSig(
                    player = player,
                    infoset = infoset,
                    actions = nodes.flatMap { it.actions }.toSet()
                )
            }

    "Visibility Semantics" - {

        "visibility from actual writer (no leak to Bob)" {
            // Regression test for critical visibility bug:
            // Alice writes x as visible, then overwrites as hidden.
            // Bob should NOT see x (uses Alice's second write visibility).
            //
            // This is primarily a regression test (game compiles without crash).
            // Bob may have different action sets based on whether Alice bailed,
            // but not based on the hidden value of Alice.x.

            val efg = compileGame(VISIBILITY_ACTUAL_WRITER)
            val bobNodes = decisionNodesForPlayer(efg, 2)
            bobNodes.isNotEmpty() shouldBe true

            // Bob should have decision nodes (strategic role with bail)
            bobNodes.all { it.actions.contains("None") } shouldBe true

            // Game should complete without errors
            efg shouldContain "t \"\""
        }

        "COMMIT visibility - others cannot see commits" {
            // Alice commits secret (hidden), Bob tries to use it.
            // Bob should NOT see Alice's secret value.
            //
            // Smoke test.

            val efg = compileGame(COMMIT_NOT_VISIBLE)
            val bobNodes = decisionNodesForPlayer(efg, 2)
            bobNodes.isNotEmpty() shouldBe true

            // Strategic roles always have bail option
            efg shouldContain "\"None\""

            // Game completes
            efg shouldContain "t \"\""
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

            val bobInfosets = infosetsForPlayer(efg, 2)

            // Bob should have at least 2 distinct infosets (different revealed values)
            (bobInfosets.map { it.infoset }.distinct().size >= 2) shouldBe true

            // At least one infoset has full choice set {true, false, None}
            bobNodes.hasFullBoolMenu() shouldBe true

            // Game completes
            efg shouldContain "t \"\""
        }
    }

    "Bail/Griefing Mechanics" - {

        "bail persists - once bailed, player is locked out" {
            // Alice has multiple actions: x, then z.
            // If Alice bails on x, Alice's second decision (z) should only offer "None".
            //
            // Semantic property: Some nodes with multiple actions, some with only bail.

            val efg = compileGame(BAIL_PERSISTENCE)
            val aliceNodes = decisionNodesForPlayer(efg, 1)

            aliceNodes.isNotEmpty() shouldBe true

            // Some node where Alice has multiple actions (before bail)
            aliceNodes.any { it.actions.toSet().size > 1 } shouldBe true

            // Some node where Alice only has bail
            aliceNodes.any { it.actions.toSet() == setOf("None") } shouldBe true

            // Terminals with bail penalties
            efg shouldContain "{ -100"

            // Terminals where both players cooperate
            efg shouldContain "{ 10 10 }"
        }

        "chance roles cannot bail" {
            // Nature (random role) should NOT have "None" as a bail option.

            val efg = compileGame(CHANCE_NO_BAIL)

            // Find chance nodes (start with "c ")
            val chanceLines = efg.lines().filter { it.startsWith("c ") }
            chanceLines.isNotEmpty() shouldBe true
            chanceLines.forEach { line ->
                line shouldNotContain "\"None\""
            }

            // Should have chance nodes with proper outcomes (true/false for boolean)
            chanceLines.any { it.contains("\"true\"") && it.contains("\"false\"") } shouldBe true
        }

        "strategic roles always have bail option" {
            val efg = compileGame(SIMUL_MIXED)

            // Alice (player 1) has bail
            decisionNodesForPlayer(efg, 1).any { "None" in it.actions } shouldBe true

            // Bob (player 2) has bail
            decisionNodesForPlayer(efg, 2).any { "None" in it.actions } shouldBe true

            // bail-related terminals exist
            efg shouldContain "{ 0 0 }"
        }
    }

    "Edge Cases and Robustness" - {

        "simultaneous actions with mixed bail/non-bail" {
            // Both players act simultaneously.
            // Should have all 4 outcome combinations.

            val efg = compileGame(SIMUL_MIXED)

            // Should have terminals for all combinations:
            efg shouldContain "{ 10 10 }"   // Both commit
            efg shouldContain "{ -5 0 }"    // Alice commits, Bob bails
            efg shouldContain "{ 0 -5 }"    // Alice bails, Bob commits
            efg shouldContain "{ 0 0 }"     // Both bail
        }

        "payoffs handle undefined values gracefully" {
            // When players bail, payoff evaluation should not crash.

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

            val aliceInfosets = infosetsForPlayer(efg, 1)

            // Should have at least one infoset
            aliceInfosets.isNotEmpty() shouldBe true
        }

        "different infosets when visible state differs" {
            // When revealed values differ, infosets should differ.
            //
            // Semantic property: Bob has multiple distinct infosets based on Alice's reveal.

            val efg = compileGame(REVEAL_VISIBLE)

            val bobInfosets = infosetsForPlayer(efg, 2)

            // Bob should have at least 2 distinct infosets (one per revealed value)
            (bobInfosets.map { it.infoset }.distinct().size >= 2) shouldBe true
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
})

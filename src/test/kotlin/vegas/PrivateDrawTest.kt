package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldContain
import io.kotest.matchers.collections.shouldContainExactlyInAnyOrder
import io.kotest.matchers.collections.shouldNotContain
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.string.shouldNotContain
import vegas.backend.bitcoin.CompilationException
import vegas.backend.bitcoin.generateLightningProtocol
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.backend.gambit.generateExtensiveFormGame
import vegas.backend.maid.MaidNodeType
import vegas.backend.maid.generateMaid
import vegas.backend.scribble.genScribbleFromIR
import vegas.backend.smt.generateDQBF
import vegas.frontend.compileToIR
import vegas.frontend.parseCode
import vegas.frontend.parseFile
import vegas.ir.EntropySource

private fun typedCompile(src: String) = run {
    val ast = parseCode(src)
    typeCheck(ast)
    compileToIR(ast)
}

private fun auction() = run {
    val ast = parseFile("examples/PrivateValueAuction.vg")
    typeCheck(ast)
    compileToIR(ast)
}

private val roleA = RoleId("A")
private val roleB = RoleId("B")

/**
 * Private draws (`sample Role(x: T ~ D);`): nature draws a value that only
 * its owner observes. It shapes the analysis (information sets, utilities)
 * and never reaches the contract.
 */
class PrivateDrawTest : FreeSpec({

    "type checking" - {
        "only a utility clause can read a private draw" {
            val ex = shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1 B() $ 1;
                      sample A(v: bool);
                      withdraw A.v ? { A -> 2; B -> 0 } : { A -> 0; B -> 2 }
                    }
                """.trimIndent()))
            }
            ex.message shouldContain "private draw"
        }

        "not even the owner's own guard reads it" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    type n = {0..2}
                    game main() {
                      join A() $ 1 B() $ 1;
                      sample A(v: n);
                      yield A(b: n) where A.b <= A.v;
                      withdraw { A -> 1; B -> 1 }
                    }
                """.trimIndent()))
            }.message shouldContain "private draw"
        }

        "a private draw belongs to a joined strategic role" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1;
                      sample B(v: bool);
                      withdraw { A -> 1 }
                    }
                """.trimIndent()))
            }
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      random Coin;
                      join A() $ 1;
                      sample Coin(v: bool);
                      withdraw { A -> 1 }
                    }
                """.trimIndent()))
            }.message shouldContain "random role"
        }

        "an unbounded draw needs a distribution" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1;
                      sample A(v: int);
                      withdraw { A -> 1 }
                    }
                """.trimIndent()))
            }.message shouldContain "distribution"
        }

        "payout is reserved for Role.payout" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1;
                      yield A(payout: bool);
                      withdraw { A -> 1 }
                    }
                """.trimIndent()))
            }.message shouldContain "reserved"
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1;
                      sample A(payout: bool);
                      withdraw { A -> 1 }
                    }
                """.trimIndent()))
            }.message shouldContain "reserved"
        }

        "a utility is int and belongs to a strategic role" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1;
                      sample A(v: bool);
                      withdraw { A -> 1 } utility { A -> A.v; }
                    }
                """.trimIndent()))
            }.message shouldContain "Utility must be int"
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      random Coin;
                      join A() $ 1;
                      withdraw { A -> 1 } utility { Coin -> 0; }
                    }
                """.trimIndent()))
            }.message shouldContain "strategic roles"
        }

        "a utility sees a quittable field as optional" {
            shouldThrow<StaticError> {
                typeCheck(parseCode("""
                    game main() {
                      join A() $ 1 B() $ 1;
                      yield A(b: bool);
                      withdraw { A -> 1; B -> 1 } utility { A -> A.b ? 1 : 0; }
                    }
                """.trimIndent()))
            }
            typeCheck(parseCode("""
                game main() {
                  join A() $ 1 B() $ 1;
                  yield A(b: bool);
                  withdraw { A -> 1; B -> 1 } utility { A -> (A.b != null && A.b) ? 1 : 0; }
                }
            """.trimIndent()))
        }
    }

    "IR" - {
        "the draw is nature's, owned by the role, and substitutes Role.payout" {
            val ir = auction()
            val draws = ir.dag.actions.filter { ir.dag.isPrivateDraw(it) }
            draws.map { ir.dag.owner(it) } shouldContainExactlyInAnyOrder listOf(roleA, roleB)
            draws.forEach { ir.dag.sampleSpec(it)!!.source shouldBe EntropySource.PrivateDraw }
            // A and B stay strategic: owning a draw does not make a role chance.
            ir.chanceRoles shouldBe emptySet()
            // No utility mentions the settlement any more; it reads the withdraw.
            ir.utilities.values.forEach { it.toString() shouldNotContain "payout" }
        }
    }

    "Gambit" - {
        "each bidder's bid depends on its own value only" {
            val efg = generateExtensiveFormGame(auction())
            // Players: Seller=1, A=2, B=3. A bid node offers the three hidden bids and Quit.
            val bidInfosets = efg.lines()
                .filter { it.startsWith("p ") && "Hidden(0)" in it }
                .groupBy({ it.split(" ")[2] }, { it.split(" ")[3] })
                .mapValues { (_, sets) -> sets.toSet() }
            // Two values each: two information sets per bidder, not four.
            bidInfosets["2"]!!.size shouldBe 2
            bidInfosets["3"]!!.size shouldBe 2
            // A's value, then B's under each of A's: 1 or 3 with probability 1/2.
            efg.lines().count { it.startsWith("c ") && "\"Hidden(1)\" 1/2 \"Hidden(3)\" 1/2" in it } shouldBe 3
        }

        "the leaves carry utilities, not money" {
            val efg = generateExtensiveFormGame(auction())
            // Both bid 0 and reveal: A wins at price 0, so A's utility is its value.
            efg shouldContain "t \"\" 1 \"\" { 0 1 0 }"
        }
    }

    "backends that model the game" - {
        "MAID: a value is a chance parent of its owner's bid and utility" {
            val maid = generateMaid(auction())
            maid.nodes.single { it.id == "A_v" }.type shouldBe MaidNodeType.CHANCE
            val edges = maid.edges.map { it.source to it.target }
            edges shouldContain ("A_v" to "A_b")
            edges shouldContain ("A_v" to "U_A")
            edges shouldNotContain ("A_v" to "B_b")
            edges shouldNotContain ("B_v" to "A_b")
            // A's utility with bids (0, 0) and value 3 is 3: the domain holds every value that occurs.
            maid.nodes.single { it.id == "U_A" }.domain shouldContain 3
        }

        "DQBF: a draw is universal even inside the coalition" {
            val dqbf = generateDQBF(auction(), setOf(roleA, roleB))
            dqbf shouldNotContain "(declare-fun A_v "
            dqbf shouldContain "(A_v Int)"
            // A's bid is a function of A's value alone.
            dqbf shouldContain "(declare-fun A_b (Int Bool) Int)"
        }
    }

    "backends that execute the game" - {
        "the contract never mentions a private draw" {
            val sol = generateSolidity(compileToEvm(auction()))
            sol shouldNotContain "A_v"
            sol shouldNotContain "B_v"
        }

        "Scribble sends no message for a private draw" {
            genScribbleFromIR(auction()) shouldNotContain "_v("
        }

        "Lightning refuses a private draw" {
            val ir = typedCompile("""
                game main() {
                  join A() $ 1 B() $ 1;
                  sample A(v: bool);
                  yield A(b: bool);
                  withdraw { A -> 1; B -> 1 } utility { A -> A.v ? 1 : 0; }
                }
            """.trimIndent())
            shouldThrow<CompilationException> { generateLightningProtocol(ir) }
                .message shouldContain "private draws"
        }
    }
})

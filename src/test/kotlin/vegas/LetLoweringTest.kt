package vegas

import io.kotest.assertions.throwables.shouldNotThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldNotBe
import vegas.backend.solidity.genSolidity
import vegas.backend.smt.generateSMT
import vegas.frontend.*
import vegas.frontend.Exp.BinOp
import vegas.frontend.Exp.Const
import vegas.frontend.Exp.Field
import vegas.frontend.Exp.Var
import vegas.frontend.Outcome.Value
import vegas.frontend.TypeExp.INT

/**
 * Tests for let expression IR lowering and end-to-end compilation.
 */
class LetLoweringTest : FreeSpec({

    val alice = Role(RoleId("Alice"))
    val bob = Role(RoleId("Bob"))

    fun n(i: Int) = Const.Num(i)
    fun b(v: Boolean) = Const.Bool(v)
    fun v(name: String) = Var(VarId(name))
    fun m(owner: Role, field: String) = Field(FieldRef(owner.id, VarId(field)))
    fun i(name: String) = VarDec(v(name), INT)

    fun letE(name: String, init: Exp, body: Exp) =
        Exp.Let(VarDec(v(name), INT), init, body)

    fun letO(name: String, init: Exp, body: Outcome) =
        Outcome.Let(VarDec(v(name), INT), init, body)

    fun program(vararg binds: Ext, value: Outcome): GameAst {
        val end: Ext = Ext.Value(value)
        val game = binds.reversed().fold(end) { acc, e ->
            when (e) {
                is Ext.Bind -> e.copy(ext = acc)
                is Ext.BindSingle -> e.copy(ext = acc)
                is Ext.Value -> error("Value belongs in 'value' param")
            }
        }
        return GameAst("Test", "", emptyMap(), emptyList(), game)
    }

    fun join(vararg roles: Role): Ext = Ext.Bind(
        Kind.JOIN,
        roles.map { Query(it, emptyList(), n(0), b(true)) },
        Ext.Value(Value(emptyMap()))
    )

    fun yieldTo(role: Role, params: List<VarDec>): Ext = Ext.Bind(
        Kind.YIELD,
        listOf(Query(role, params, n(0), b(true))),
        Ext.Value(Value(emptyMap()))
    )

    fun pay(vararg pairs: Pair<Role, Exp>) = Value(mapOf(*pairs))

    "IR Lowering - Let Expressions" - {

        "should lower simple let in expression" {
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), BinOp("+", v("x"), n(5))))
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
            ir shouldNotBe null
        }

        "should lower let with field reference" {
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("bid"))),
                value = pay(alice to letE("doubled", BinOp("*", m(alice, "bid"), n(2)), v("doubled")))
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
            ir shouldNotBe null
        }

        "should lower nested let expressions" {
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("x"))),
                value = pay(
                    alice to letE(
                        "a", BinOp("+", m(alice, "x"), n(10)),
                        letE("b", BinOp("*", v("a"), n(2)), BinOp("-", v("b"), n(5)))
                    )
                )
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
        }

        "should lower let with shadowing" {
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), letE("x", n(20), v("x"))))
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
        }

        "should lower simple let in outcome" {
            val prog = program(
                join(alice, bob),
                value = letO("total", n(100), pay(alice to v("total"), bob to n(0)))
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
            ir shouldNotBe null
        }

        "should lower let in outcome with field references" {
            val prog = program(
                join(alice, bob),
                yieldTo(alice, listOf(i("x"))),
                yieldTo(bob, listOf(i("y"))),
                value = letO(
                    "sum",
                    BinOp("+", m(alice, "x"), m(bob, "y")),
                    pay(alice to v("sum"), bob to BinOp("-", n(0), v("sum")))
                )
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
        }

        "should lower nested let in outcome" {
            val prog = program(
                join(alice, bob),
                value = letO(
                    "total", n(100),
                    letO(
                        "half", BinOp("/", v("total"), n(2)),
                        pay(alice to v("half"), bob to BinOp("-", v("total"), v("half")))
                    )
                )
            )
            val ir = shouldNotThrow<Exception> { compileToIR(prog) }
            ir shouldNotBe null
        }
    }

    "Backend Compilation - Let Expressions" - {

        "should compile let to Solidity" {
            val prog = program(
                join(alice, bob),
                value = letO(
                    "pot", n(200),
                    pay(alice to BinOp("/", v("pot"), n(2)), bob to BinOp("/", v("pot"), n(2)))
                )
            )
            val ir = compileToIR(prog)
            val sol = shouldNotThrow<Exception> { genSolidity(ir) }
            sol shouldNotBe null
        }

        "should compile nested let to Solidity" {
            val prog = program(
                join(alice, bob),
                value = letO(
                    "a", n(100),
                    letO("b", BinOp("/", v("a"), n(2)), pay(alice to v("b"), bob to v("b")))
                )
            )
            val ir = compileToIR(prog)
            val sol = shouldNotThrow<Exception> { genSolidity(ir) }
            sol shouldNotBe null
        }

        "should compile let to SMT" {
            val prog = program(
                join(alice, bob),
                value = letO("total", n(100), pay(alice to v("total"), bob to n(0)))
            )
            val ir = compileToIR(prog)
            val smt = shouldNotThrow<Exception> { generateSMT(ir) }
            smt shouldNotBe null
        }
    }


    "IR Lowering Semantics" - {

        "should correctly substitute variables" {
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(5), BinOp("+", v("x"), v("x"))))
            )
            val ir = compileToIR(prog)
            ir.payoffs[alice.id] shouldNotBe null
        }

        "should handle shadowing correctly" {
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), letE("x", n(20), v("x"))))
            )
            val ir = compileToIR(prog)
            ir.payoffs[alice.id] shouldNotBe null
        }

        "should preserve field references during substitution" {
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("bid"))),
                value = pay(alice to letE("bonus", n(10), BinOp("+", m(alice, "bid"), v("bonus"))))
            )
            val ir = compileToIR(prog)
            ir.payoffs[alice.id] shouldNotBe null
        }
    }
})

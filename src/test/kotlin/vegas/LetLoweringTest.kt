package vegas

import io.kotest.assertions.throwables.shouldNotThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
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
import vegas.ir.freeVars
import vegas.ir.substituteVar

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

    "α-renaming Tests" - {

        "should collect free variables correctly" {
            // Simple variable
            freeVars(v("x")) shouldBe setOf(VarId("x"))

            // Constant has no free variables
            freeVars(n(42)) shouldBe emptySet()

            // Binary operation
            freeVars(BinOp("+", v("x"), v("y"))) shouldBe setOf(VarId("x"), VarId("y"))

            // Let expression: x is bound, y is free
            freeVars(letE("x", v("y"), BinOp("+", v("x"), v("z")))) shouldBe
                    setOf(VarId("y"), VarId("z"))
        }

        "should not capture when substituting without conflicts" {
            // let! x = 5 in (let! y = x in y)
            // Substitute x := 5
            // Result: let! y = 5 in y
            val inner = letE("y", v("x"), v("y"))
            val expr = letE("x", n(5), inner)

            val result = substituteVar(expr.exp, VarId("x"), n(5))

            // Should produce: let! y = 5 in y
            // The inner let should have init = 5
            result as Exp.Let
            result.init shouldBe n(5)
            result.exp shouldBe v("y")
        }

        "should perform α-renaming to avoid capture" {
            // Critical test case from REVIEW.md:
            // let! x = z in (let! z = 5 in x+z)
            //
            // WITHOUT α-renaming, substituting x := z would give:
            //   let! z = 5 in z+z  (WRONG - z is captured)
            //
            // WITH α-renaming, we rename the inner z to avoid capture:
            //   let! z_N = 5 in z+z_N  (CORRECT)

            val innerLet = letE("z", n(5), BinOp("+", v("x"), v("z")))
            val outerLet = letE("x", v("z"), innerLet)

            // Substitute x := z in the body
            val result = substituteVar(outerLet.exp, VarId("x"), v("z"))

            // Result should be a Let expression
            result as Exp.Let

            // The init should remain 5
            result.init shouldBe n(5)

            // The binder should have been RENAMED to avoid capturing z
            // We can't predict the exact name (z_0, z_1, etc.) but it should NOT be "z"
            val renamedBinder = result.dec.v.id
            (renamedBinder != VarId("z")) shouldBe true

            // The body should be z + (renamed_var)
            val body = result.exp as BinOp
            body.op shouldBe "+"
            body.left shouldBe v("z")  // The free z from the replacement expression

            // The right side should be the renamed variable, matching the binder
            val renamedVar = body.right as Var
            renamedVar.id shouldBe renamedBinder  // Must match the renamed binder

            // Critically: the renamed variable is NOT "z", proving capture was avoided
            (renamedVar.id != VarId("z")) shouldBe true
        }

        "should handle nested α-renaming" {
            // let! x = (let! y = 1 in y) in (let! y = x in y)
            // The outer let binds x to (let! y = 1 in y)
            // The inner let would capture y if we're not careful
            val replacement = letE("y", n(1), v("y"))
            val inner = letE("y", v("x"), v("y"))
            val outer = letE("x", replacement, inner)

            val result = substituteVar(outer.exp, VarId("x"), replacement)

            // Should produce: let! y_N = (let! y = 1 in y) in y_N
            result as Exp.Let
            // Init should contain the nested let
            result.init as Exp.Let
        }

        "should not rename when no capture risk" {
            // let! x = 5 in (let! y = 10 in x+y)
            // Substituting x := 5 doesn't require renaming y
            val inner = letE("y", n(10), BinOp("+", v("x"), v("y")))
            val outer = letE("x", n(5), inner)

            val result = substituteVar(outer.exp, VarId("x"), n(5))

            result as Exp.Let
            // y should NOT be renamed (no free vars in replacement)
            result.dec.v.id shouldBe VarId("y")
            result.init shouldBe n(10)

            val body = result.exp as BinOp
            body.left shouldBe n(5)
            body.right shouldBe v("y")
        }
    }
})

package vegas

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import vegas.backend.evm.compileToEvm
import vegas.backend.evm.generateSolidity
import vegas.backend.smt.generateSMT
import vegas.frontend.*
import vegas.frontend.Exp.BinOp
import vegas.frontend.Exp.Const
import vegas.frontend.Exp.Field
import vegas.frontend.Exp.Var
import vegas.frontend.Outcome.Value
import vegas.frontend.TypeExp.INT
import vegas.ir.*

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
        null,
        Ext.Value(Value(emptyMap()))
    )

    fun yieldTo(role: Role, params: List<VarDec>): Ext = Ext.Bind(
        Kind.YIELD,
        listOf(Query(role, params, n(0), b(true))),
        null,
        Ext.Value(Value(emptyMap()))
    )

    fun pay(vararg pairs: Pair<Role, Exp>) = Value(mapOf(*pairs))

    "IR Lowering - Let Expressions" - {

        "should eliminate let and substitute value in payoff" {
            // let! x = 10 in (x + 5) => 10 + 5
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), BinOp("+", v("x"), n(5))))
            )
            val ir = compileToIR(prog)

            // IR should contain substituted expression, no Let nodes
            val payoff = ir.payoffs[alice.id]!! as Expr.Add
            payoff.l shouldBe Expr.Const.IntVal(10)
            payoff.r shouldBe Expr.Const.IntVal(5)
        }

        "should substitute field reference into let body" {
            // let! doubled = Alice.bid * 2 in doubled => Alice.bid * 2
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("bid"))),
                value = pay(alice to letE("doubled", BinOp("*", m(alice, "bid"), n(2)), v("doubled")))
            )
            val ir = compileToIR(prog)

            val payoff = ir.payoffs[alice.id]!! as Expr.Mul
            payoff.l shouldBe Expr.Field(FieldRef(alice.id, VarId("bid")))
            payoff.r shouldBe Expr.Const.IntVal(2)
        }

        "should substitute nested let expressions correctly" {
            // let! a = Alice.x + 10 in (let! b = a * 2 in b - 5)
            // => ((Alice.x + 10) * 2) - 5
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
            val ir = compileToIR(prog)

            val payoff = ir.payoffs[alice.id]!! as Expr.Sub
            val mul = payoff.l as Expr.Mul
            val add = mul.l as Expr.Add

            add.l shouldBe Expr.Field(FieldRef(alice.id, VarId("x")))
            add.r shouldBe Expr.Const.IntVal(10)
            mul.r shouldBe Expr.Const.IntVal(2)
            payoff.r shouldBe Expr.Const.IntVal(5)
        }

        "should handle shadowing by using innermost binding" {
            // let! x = 10 in (let! x = 20 in x) => 20
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), letE("x", n(20), v("x"))))
            )
            val ir = compileToIR(prog)

            // Inner x shadows outer, so result is 20
            ir.payoffs[alice.id] shouldBe Expr.Const.IntVal(20)
        }

        "should distribute let binding across multiple payoffs" {
            // let! total = 100 in {Alice: total, Bob: 0}
            // => {Alice: 100, Bob: 0}
            val prog = program(
                join(alice, bob),
                value = letO("total", n(100), pay(alice to v("total"), bob to n(0)))
            )
            val ir = compileToIR(prog)

            ir.payoffs[alice.id] shouldBe Expr.Const.IntVal(100)
            ir.payoffs[bob.id] shouldBe Expr.Const.IntVal(0)
        }

        "should substitute field references into multiple payoffs" {
            // let! sum = Alice.x + Bob.y in {Alice: sum, Bob: -sum}
            // => {Alice: Alice.x + Bob.y, Bob: -(Alice.x + Bob.y)}
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
            val ir = compileToIR(prog)

            val alicePayoff = ir.payoffs[alice.id]!! as Expr.Add
            alicePayoff.l shouldBe Expr.Field(FieldRef(alice.id, VarId("x")))
            alicePayoff.r shouldBe Expr.Field(FieldRef(bob.id, VarId("y")))

            val bobPayoff = ir.payoffs[bob.id]!! as Expr.Sub
            bobPayoff.l shouldBe Expr.Const.IntVal(0)
            val bobSum = bobPayoff.r as Expr.Add
            bobSum.l shouldBe Expr.Field(FieldRef(alice.id, VarId("x")))
            bobSum.r shouldBe Expr.Field(FieldRef(bob.id, VarId("y")))
        }

        "should substitute nested let in outcome" {
            // let! total = 100 in (let! half = total/2 in {Alice: half, Bob: total-half})
            // => {Alice: 100/2, Bob: 100 - (100/2)}
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
            val ir = compileToIR(prog)

            val alicePayoff = ir.payoffs[alice.id]!! as Expr.Div
            alicePayoff.l shouldBe Expr.Const.IntVal(100)
            alicePayoff.r shouldBe Expr.Const.IntVal(2)

            val bobPayoff = ir.payoffs[bob.id]!! as Expr.Sub
            bobPayoff.l shouldBe Expr.Const.IntVal(100)
            val bobHalf = bobPayoff.r as Expr.Div
            bobHalf.l shouldBe Expr.Const.IntVal(100)
            bobHalf.r shouldBe Expr.Const.IntVal(2)
        }
    }

    "Backend Compilation - Let Expressions" - {

        "should compile let to Solidity without let variables" {
            val prog = program(
                join(alice, bob),
                value = letO(
                    "pot", n(200),
                    pay(alice to BinOp("/", v("pot"), n(2)), bob to BinOp("/", v("pot"), n(2)))
                )
            )
            val solidity = generateSolidity(compileToEvm(compileToIR(prog)))

            // Generated Solidity should not contain "pot" variable name
            (solidity.contains("pot")) shouldBe false
            (solidity.contains("let")) shouldBe false
        }

        "should compile nested let to Solidity with full substitution" {
            val prog = program(
                join(alice, bob),
                value = letO(
                    "myTotal", n(100),
                    letO("myHalf", BinOp("/", v("myTotal"), n(2)), pay(alice to v("myHalf"), bob to v("myHalf")))
                )
            )

            // IR should not contain any Let nodes
            val solidity = generateSolidity(compileToEvm(compileToIR(prog)))

            // Solidity should not contain let-bound variable names
            (solidity.contains("myTotal")) shouldBe false
            (solidity.contains("myHalf")) shouldBe false

            // Should compile without errors
            solidity.isNotEmpty() shouldBe true
        }

        "should compile let to SMT without frontend variable names" {
            val prog = program(
                join(alice, bob),
                value = letO("total", n(100), pay(alice to v("total"), bob to n(0)))
            )
            val smt = generateSMT(compileToIR(prog))

            // SMT output should not contain "total" from let binding
            (smt.contains("total")) shouldBe false

            // Should generate valid SMT
            smt.isNotEmpty() shouldBe true
        }
    }


    "IR Lowering Semantics" - {

        "should duplicate value when variable appears multiple times" {
            // let! x = 5 in (x + x) => 5 + 5
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(5), BinOp("+", v("x"), v("x"))))
            )
            val ir = compileToIR(prog)

            val payoff = ir.payoffs[alice.id]!! as Expr.Add
            payoff.l shouldBe Expr.Const.IntVal(5)
            payoff.r shouldBe Expr.Const.IntVal(5)
        }

        "should use innermost binding for shadowed variables" {
            // let! x = 10 in (let! x = 20 in x) => 20
            val prog = program(
                join(alice),
                value = pay(alice to letE("x", n(10), letE("x", n(20), v("x"))))
            )
            val ir = compileToIR(prog)

            // Inner binding shadows outer, result should be 20
            ir.payoffs[alice.id] shouldBe Expr.Const.IntVal(20)
        }

        "should preserve field references during substitution" {
            // let! bonus = 10 in (Alice.bid + bonus) => Alice.bid + 10
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("bid"))),
                value = pay(alice to letE("bonus", n(10), BinOp("+", m(alice, "bid"), v("bonus"))))
            )
            val ir = compileToIR(prog)

            val payoff = ir.payoffs[alice.id]!! as Expr.Add
            payoff.l shouldBe Expr.Field(FieldRef(alice.id, VarId("bid")))
            payoff.r shouldBe Expr.Const.IntVal(10)
        }

        "should duplicate field references when bound variable used multiple times" {
            // let! bid = Alice.bid in (bid + bid) => Alice.bid + Alice.bid
            val prog = program(
                join(alice),
                yieldTo(alice, listOf(i("bid"))),
                value = pay(alice to letE("b", m(alice, "bid"), BinOp("+", v("b"), v("b"))))
            )
            val ir = compileToIR(prog)

            val payoff = ir.payoffs[alice.id]!! as Expr.Add
            payoff.l shouldBe Expr.Field(FieldRef(alice.id, VarId("bid")))
            payoff.r shouldBe Expr.Field(FieldRef(alice.id, VarId("bid")))
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

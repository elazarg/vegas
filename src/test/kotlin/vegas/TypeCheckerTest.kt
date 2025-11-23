package vegas

import vegas.frontend.Exp.*
import vegas.frontend.Outcome.*
import vegas.frontend.TypeExp.*
import io.kotest.assertions.throwables.shouldNotThrow
import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import io.kotest.matchers.string.shouldContain
import vegas.frontend.Exp
import vegas.frontend.GameAst
import vegas.frontend.Ext
import vegas.frontend.Kind
import vegas.frontend.Outcome
import vegas.frontend.Query
import vegas.frontend.Role
import vegas.frontend.TypeExp
import vegas.frontend.VarDec
import vegas.ir.desugar

// -------- Test-local builders --------
private object B {
    // literals
    fun n(i: Int) = Const.Num(i)
    fun b(v: Boolean) = Const.Bool(v)
    fun addr(i: Int) = Const.Address(i)
    fun hid(e: Const) = Const.Hidden(e)

    // variables / members
    fun v(name: String) = Var(VarId(name))
    fun m(role: Role, field: String) = Field(FieldRef(role.id, VarId(field)))

    fun not(e: Exp) = UnOp("!", e)
    fun isDef(e: Exp) = UnOp("isDefined", e)
    fun isUndef(e: Exp) = UnOp("isUndefined", e)
    fun abs(e: Exp) = Call(v("abs"), listOf(e))

    fun ite(c: Exp, t: Exp, f: Exp) = Exp.Cond(c, t, f)

    // let (expression & outcome)
    fun letE(name: String, t: TypeExp, init: Exp, body: Exp) =
        Exp.Let(VarDec(v(name), t), init, body)

    fun letO(name: String, t: TypeExp, init: Exp, body: Outcome) =
        Outcome.Let(VarDec(v(name), t), init, body)

    // param declarations
    fun dec(name: String, t: String) = VarDec(v(name), TypeId(t))
    fun dec(name: String, t: TypeExp) = VarDec(v(name), t)
    fun i(name: String) = VarDec(v(name), INT)
    fun bl(name: String) = VarDec(v(name), BOOL)
    fun opt(t: TypeExp) = Opt(t)
    fun hidden(t: TypeExp) = Hidden(t)

    // queries and binds
    private fun q(role: Role, params: List<VarDec> = emptyList(), deposit: Int = 0, where: Exp = b(true)) =
        Query(role = role, params = params, deposit = n(deposit), where = where)

    fun join(role: Role, params: List<VarDec> = emptyList(), deposit: Int = 0, where: Exp = b(true)) =
        Ext.Bind(Kind.JOIN, listOf(q(role, params, deposit, where)), Ext.Value(Value(emptyMap())))

    fun yieldTo(role: Role, params: List<VarDec>, where: Exp = b(true)) =
        Ext.Bind(Kind.YIELD, listOf(q(role, params, 0, where)), Ext.Value(Value(emptyMap())))

    fun reveal(role: Role, params: List<VarDec>, where: Exp = b(true)) =
        Ext.Bind(Kind.REVEAL, listOf(q(role, params, 0, where)), Ext.Value(Value(emptyMap())))

    fun joinChance(role: Role, where: Exp = b(true)) =
        Ext.Bind(Kind.JOIN_CHANCE, listOf(q(role, emptyList(), 0, where)), Ext.Value(Value(emptyMap())))

    // payouts
    fun pay(vararg outs: Pair<Role, Exp>) = Value(mapOf(*outs))

    /**
     * Program builder per request:
     *  program(types, binds..., value?)
     *
     * Threads binds left->right and attaches an optional final Value.
     */
    fun program(
        types: Map<TypeId, TypeExp>,
        vararg binds: Ext,
        value: Value? = null,
        name: String = "TestProgram"
    ): GameAst {
        val end: Ext = Ext.Value(value ?: Value(emptyMap()))
        val game = binds.reversed().fold(end) { acc, e ->
            when (e) {
                is Ext.Bind -> e.copy(ext = acc)
                is Ext.BindSingle -> e.copy(ext = acc)
                is Ext.Value -> error("Value belongs in 'value' param")
            }
        }
        return GameAst(name, desc = "", types = types, game = game)
    }

    fun program(
        vararg binds: Ext,
        value: Value? = null,
        name: String = "TestProgram"
    ): GameAst {
        return program(emptyMap(), binds = binds, value = value, name = name)
    }
}

// arithmetic & logic (only what we use here)
infix fun Exp.plus(r: Exp) = BinOp("+", this, r)
infix fun Exp.minus(r: Exp) = BinOp("-", this, r)
infix fun Exp.times(r: Exp) = BinOp("*", this, r)
infix fun Exp.div(r: Exp) = BinOp("/", this, r)
infix fun Exp.lt(r: Exp) = BinOp("<", this, r)
infix fun Exp.gt(r: Exp) = BinOp(">", this, r)
infix fun Exp.lte(r: Exp) = BinOp("<=", this, r)
infix fun Exp.gte(r: Exp) = BinOp(">=", this, r)
infix fun Exp.and(r: Exp) = BinOp("&&", this, r)
infix fun Exp.or(r: Exp) = BinOp("||", this, r)
infix fun Exp.eq(r: Exp) = BinOp("==", this, r)
infix fun Exp.neq(r: Exp) = BinOp("!=", this, r)
infix fun Exp.iff(r: Exp) = BinOp("<->", this, r)
infix fun Exp.xnor(r: Exp) = BinOp("<-!->", this, r)

fun role(name: String) = Role(RoleId(name))

val Q = role("Q")
val P = role("P")
val P1 = role("P1")
val P2 = role("P2")
val P3 = role("P3")
val H = role("H")
val Host = role("Host")
val Guest = role("Guest")
val Alice = role("Alice")
val Bob = role("Bob")

class TypeCheckerTest : FreeSpec({

    "Type System - Basic Types" - {
        "should accept valid primitive types" - {
            data class ValidCase(val prog: GameAst, val description: String)

            withData(
                ValidCase(
                    B.program(B.join(P), B.yieldTo(P, listOf(B.i("x")))),
                    "integer parameter"
                ),
                ValidCase(
                    B.program(B.join(P), B.yieldTo(P, listOf(B.bl("b")))),
                    "boolean parameter"
                ),
                ValidCase(
                    B.program(B.join(P), B.yieldTo(P, listOf(B.i("x"), B.bl("b")))),
                    "multiple parameters"
                ),
                ValidCase(
                    B.program(B.join(P, deposit = 100)),
                    "integer deposit"
                ),
                ValidCase(
                    B.program(B.join(P), value = B.pay(P to B.n(42))),
                    "integer payout"
                ),
                ValidCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.i("x"))),
                        value = B.pay(P to B.m(P, "x"))
                    ),
                    "member access returning int"
                )
            ) { case ->
                shouldNotThrow<StaticError> {
                    typeCheck(case.prog)
                }
            }
        }


        "should reject type mismatches in basic expressions" - {
            data class TypeMismatchCase(val prog: GameAst, val expectedError: String)

            withData(
                TypeMismatchCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.i("x"))),
                        value = B.pay(P to (B.m(P, "x") and B.b(true)))
                    ),
                    "Incompatible"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.bl("b"))),
                        value = B.pay(P to (B.m(P, "b") plus B.n(1)))
                    ),
                    "Incompatible"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.i("x"))),
                        value = B.pay(
                            P to B.ite(
                                B.m(P, "x") gt B.b(true),  // int > bool -> error
                                B.n(1),
                                B.n(0)
                            )
                        )
                    ),
                    "Incompatible"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P),
                        value = B.pay(P to B.b(true))  // outcome must be int
                    ),
                    "Outcome value must be an int"
                )
            ) { case ->
                val exception = shouldThrow<StaticError> {
                    typeCheck(case.prog)
                }
                exception.message shouldContain case.expectedError
            }
        }

    }

    "Type System - Custom Types" - {

        "should handle finite set types correctly" - {
            withData(
                // type door = {0,1,2}; join P(); yield P(d: door)
                B.program(
                    types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                    B.join(P),
                    B.yieldTo(
                        P, listOf(B.dec("d", TypeId("door")))
                    )
                ),
                // type coin = {0,1}; join P(); yield P(flip: coin)
                B.program(
                    types = mapOf(TypeId("coin") to Subset(setOf(B.n(0), B.n(1)))),
                    B.join(P),
                    B.yieldTo(P, listOf(B.dec("flip", TypeId("coin"))))
                ),
                // type small, big sets; yield both
                B.program(
                    types = mapOf(
                        TypeId("small") to Subset(setOf(B.n(1), B.n(2), B.n(3))),
                        TypeId("big") to Subset(setOf(B.n(10), B.n(20), B.n(30)))
                    ),
                    B.join(P),
                    B.yieldTo(P, listOf(B.dec("s", TypeId("small")), B.dec("b", TypeId("big"))))
                )
            ) { prog ->
                shouldNotThrow<StaticError> { typeCheck(prog) }
            }
        }

        "should handle range types correctly" - {
            withData(
                B.program(
                    types = mapOf(TypeId("digit") to Range(B.n(0), B.n(9))),
                    B.join(P),
                    B.yieldTo(P, listOf(B.dec("d", TypeId("digit"))))
                ),
                B.program(
                    types = mapOf(TypeId("percent") to Range(B.n(0), B.n(100))),
                    B.join(P),
                    B.yieldTo(P, listOf(B.dec("p", TypeId("percent"))))
                )
            ) { prog ->
                shouldNotThrow<StaticError> { typeCheck(prog) }
            }
        }

        "should validate where clauses with custom types" - {

            "accepts valid where constraints" {
                val validCases = listOf(
                    B.program(
                        types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                        B.join(P),
                        B.yieldTo(
                            P,
                            listOf(B.dec("d", TypeId("door"))),
                            where = B.m(P, "d") neq B.n(1)
                        )
                    ),
                    B.program(
                        types = mapOf(TypeId("coin") to Subset(setOf(B.n(0), B.n(1)))),
                        B.join(P),
                        B.yieldTo(
                            P,
                            listOf(B.dec("c", TypeId("coin"))),
                            where = (B.m(P, "c") eq B.n(0)) or (B.m(P, "c") eq B.n(1))
                        )
                    ),
                    B.program(
                        types = mapOf(TypeId("range") to Range(B.n(1), B.n(10))),
                        B.join(P),
                        B.yieldTo(
                            P,
                            listOf(B.dec("r", TypeId("range"))),
                            where = B.m(P, "r") gt B.n(5)
                        )
                    )
                )
                validCases.forEach { p ->
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "rejects invalid where constraints" {
                val bad = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.i("x")), where = B.m(P, "x")) // non-boolean where
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "Where clause failed"
            }
        }
    }

    "Type System - Hidden Types" - {

        "should handle hidden type declarations" - {
            withData(
                // join H(); yield H(secret: hidden int)
                B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.dec("secret", B.hidden(INT))))
                ),
                // type door = {0,1,2}; join H(); yield H(car: hidden door)
                B.program(
                    types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                    B.join(H),
                    B.yieldTo(H, listOf(B.dec("car", B.hidden(TypeId("door")))))
                ),
                // join H(); yield H(x: hidden int, y: int)
                B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.dec("x", B.hidden(INT)), B.dec("y", INT)))
                ),
                // join H(); yield H(a: hidden bool, b: hidden bool)
                B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.dec("a", B.hidden(BOOL)), B.dec("b", B.hidden(BOOL))))
                )
            ) { prog ->
                shouldNotThrow<StaticError> { typeCheck(prog) }
            }
        }

        "should validate reveal operations" - {

            "accepts revealing hidden values" {
                val validReveals = listOf(
                    // join H(); yield H(s: hidden int); reveal H(s: int)
                    B.program(
                        B.join(H),
                        B.yieldTo(H, listOf(B.dec("s", B.hidden(INT)))),
                        B.reveal(H, listOf(B.dec("s", INT)))
                    ),
                    // type door = {0,1,2}; join H(); yield H(car: hidden door); reveal H(car: door)
                    B.program(
                        types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                        B.join(H),
                        B.yieldTo(H, listOf(B.dec("car", B.hidden(TypeId("door"))))),
                        B.reveal(H, listOf(B.dec("car", TypeId("door"))))
                    ),
                    // join H(); yield H(a: hidden int, b: hidden bool); reveal H(a: int, b: bool)
                    B.program(
                        B.join(H),
                        B.yieldTo(H, listOf(B.dec("a", B.hidden(INT)), B.dec("b", B.hidden(BOOL)))),
                        B.reveal(H, listOf(B.dec("a", INT), B.dec("b", BOOL)))
                    )
                )
                validReveals.forEach { p ->
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "rejects revealing non-hidden values" {
                val bad = B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.i("public"))),
                    B.reveal(H, listOf(B.i("public")))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "must be hidden"
            }

            "rejects type mismatches in reveal" {
                val bad = B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.dec("s", B.hidden(INT)))),
                    B.reveal(H, listOf(B.bl("s"))) // mismatch: int vs bool
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                // just assert that an error message was produced (type mismatch)
                ex.message shouldContain "Reveal type mismatch for 'H.s': expected int, got bool"
            }
        }
    }
    "Type System - Roles and Field Access" - {

        "should validate role declarations" - {

            "accepts valid role usage" {
                val validRoles = listOf(
                    B.program(B.join(Host), B.join(Guest)),
                    B.program(B.join(P, deposit = 100), B.join(Q, deposit = 200)),
                    B.program(B.join(P), B.join(P1), B.join(P2), B.join(P3))
                )
                validRoles.forEach { prog ->
                    shouldNotThrow<StaticError> { typeCheck(prog) }
                }
            }

            "accepts valid member access" {
                val p = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.i("x"), B.bl("y"))),
                    value = B.pay(P to B.ite(B.m(P, "x") eq B.n(5), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(p) }
            }

            "rejects accessing undefined roles" {
                val bad = B.program(
                    B.yieldTo(role("UnknownRole"), listOf(B.i("x")))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "UnknownRole is not a role"
            }

            "rejects accessing undefined members" {
                val bad = B.program(
                    B.join(P),
                    value = B.pay(P to B.m(P, "undefined"))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "undefined"
            }
        }

        "should handle role scoping correctly" - {

            "member access requires role in scope" {
                val bad = B.program(
                    B.join(P),
                    B.yieldTo(Q, listOf(B.i("x"))), // Q never joined
                    value = B.pay(P to B.m(Q, "x"))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "Q is not a role"
            }

            "cross-role member access in multi-player games" {
                val p = B.program(
                    B.join(P1), B.join(P2),
                    B.yieldTo(P1, listOf(B.i("x"))),
                    B.yieldTo(P2, listOf(B.i("y"))),
                    value = Value(
                        mapOf(
                            P1 to B.ite(B.m(P2, "y") gt B.m(P1, "x"), B.n(100), B.n(0)),
                            P2 to B.ite(B.m(P1, "x") gt B.m(P2, "y"), B.n(100), B.n(0))
                        )
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(p) }
            }
        }
    }
    "Type System - Operators" - {

        "arithmetic operators require integers" - {
            data class ArithmeticCase(val expr: Exp, val valid: Boolean)

            withData(
                ArithmeticCase(B.n(5) plus B.n(3), true),
                ArithmeticCase(B.n(10) minus B.n(7), true),
                ArithmeticCase(B.n(4) times B.n(2), true),
                ArithmeticCase(B.n(8) div B.n(2), true),
                ArithmeticCase(B.b(true) plus B.n(5), false),
                ArithmeticCase(B.n(5) times B.b(false), false),
                ArithmeticCase(B.b(true) minus B.b(false), false),
            ) { case ->
                val prog = B.program(
                    B.join(P),
                    value = B.pay(P to case.expr)
                )
                if (case.valid) {
                    shouldNotThrow<StaticError> { typeCheck(prog) }
                } else {
                    shouldThrow<StaticError> { typeCheck(prog) }
                }
            }
        }

        "comparison operators" - {

            "accept integer comparisons" {
                val valid = listOf(
                    B.n(5) lt B.n(10),
                    B.n(3) lte B.n(3),
                    B.n(7) gt B.n(2),
                    B.n(4) gte B.n(4)
                )
                valid.forEach { cmp ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(cmp, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "reject non-integer comparisons" {
                val invalid = listOf(
                    B.b(true) lt B.b(false),
                    B.n(5) gt B.b(true),
                    B.b(false) lte B.n(3)
                )
                invalid.forEach { cmp ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(cmp, B.n(1), B.n(0)))
                    )
                    shouldThrow<StaticError> { typeCheck(p) }
                }
            }
        }

        "boolean operators require booleans" - {

            "accept valid boolean operations" {
                val valid = listOf<Exp>(
                    B.b(true) and B.b(false),
                    B.b(true) or B.b(false),
                    B.not(B.b(true)),
                    B.not(B.b(true) and B.b(false))
                )
                valid.forEach { bexpr ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(bexpr, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "reject invalid boolean operations" {
                val invalid = listOf<Exp>(
                    B.n(5) and B.b(true),
                    B.b(false) or B.n(3),
                    B.not(B.n(42))
                )
                invalid.forEach { bexpr ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(bexpr, B.n(1), B.n(0)))
                    )
                    val ex = shouldThrow<StaticError> { typeCheck(p) }
                    ex.message shouldContain "Incompatible"
                }
            }
        }

        "equality operators" - {

            "accept compatible type comparisons" {
                val valid = listOf<Exp>(
                    B.n(5) eq B.n(5),
                    B.b(true) eq B.b(false),
                    B.n(3) neq B.n(7),
                    B.b(true) neq B.b(true)
                )
                valid.forEach { eqexpr ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(eqexpr, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "special iff operators (<->, <-!->)" {
                val p1 = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.bl("a"), B.bl("b"))),
                    value = B.pay(P to B.ite(B.m(P, "a") iff B.m(P, "b"), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(p1) }

                val p2 = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.bl("a"), B.bl("b"))),
                    value = B.pay(P to B.ite(B.m(P, "a") xnor B.m(P, "b"), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(p2) }
            }
        }

        "null checking operators" - {

            "isDefined and isUndefined" {
                val p1 = B.program(
                    B.join(P), B.join(Q),
                    B.yieldTo(P, listOf(B.dec("x", B.opt(INT)))), // <-- make x optional
                    value = Value(
                        mapOf(
                            P to B.ite(B.isDef(B.m(P, "x")), B.n(100), B.n(0)), // int on both branches
                            Q to B.ite(B.isDef(B.m(P, "x")), B.n(0), B.n(100))
                        )
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(p1) }

                // Cannot return P.opt (opt(int)) as an int payout without an explicit unwrap/default.
                val p2a = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.dec("opt", B.opt(INT)))),
                    value = B.pay(
                        P to B.ite(B.isUndef(B.m(P, "opt")), B.n(-100), B.n(0)) // both int
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(p2a) }
            }
        }
    }

    "Type System - Conditional Expressions" - {

        "should type check ternary conditionals" - {

            "accepts well-typed conditionals" {
                val validConditionals = listOf(
                    B.ite(B.b(true), B.n(5), B.n(10)),
                    B.ite(B.n(5) gt B.n(3), B.n(100), B.n(200)),
                    B.ite(B.b(false), B.n(1), B.n(0))
                )

                validConditionals.forEach { expr ->
                    val p = B.program(
                        B.join(P),
                        value = B.pay(P to expr)
                    )
                    shouldNotThrow<StaticError> { typeCheck(p) }
                }
            }

            "rejects non-boolean conditions" {
                val bad = B.program(
                    B.join(P),
                    value = B.pay(P to B.ite(B.n(5), B.n(10), B.n(20)))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "Expected bool, actual int"
            }

            "reject non-numerical outcome" {
                val types = mapOf(
                    TypeId("small") to Subset(setOf(B.n(1), B.n(2), B.n(3))),
                    TypeId("big") to Subset(setOf(B.n(10), B.n(20), B.n(30)))
                )
                val bad = B.program(
                    types,
                    B.join(P),
                    B.yieldTo(P, listOf(B.bl("b"), B.dec("s", TypeId("small")), B.dec("g", TypeId("big")))),
                    value = B.pay(P to B.ite(B.m(P, "b"), B.m(P, "s"), B.m(P, "g")))
                )
                val ex = shouldThrow<StaticError> { typeCheck(bad) }
                ex.message shouldContain "Outcome value must be an int"
            }
        }

        "should handle nested conditionals" {
            val nested = B.ite(
                B.m(P, "x") gt B.n(10),
                B.ite(B.m(P, "y") gt B.n(5), B.n(100), B.n(50)),
                B.ite(B.m(P, "y") gt B.n(5), B.n(25), B.n(0))
            )
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("x"), B.i("y"))),
                value = B.pay(P to nested)
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }
    }

    "Type System - Let Expressions" - {

        "should handle let bindings in expressions" {
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("x"))),
                value = B.pay(
                    P to B.letE(
                        "y", INT,
                        B.m(P, "x") plus B.n(10),
                        B.v("y") times B.n(2)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "should handle let bindings in outcomes" {
            val p = B.program(
                B.join(P), B.join(Q),
                B.yieldTo(P, listOf(B.i("x"))),
                value = B.letO(
                    "total", INT,
                    B.m(P, "x") times B.n(100),
                    Value(
                        mapOf(
                            P to B.v("total"),
                            Q to BinOp("-", B.n(0), B.v("total"))
                        )
                    )
                ).let { desugar(it) } // convert Outcome.Let -> Value
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "should reject type mismatches in let initialization" {
            val bad = B.program(
                B.join(P),
                value = B.pay(
                    P to B.letE("x", INT, B.b(true), B.v("x") plus B.n(5))
                )
            )
            val ex = shouldThrow<StaticError> { typeCheck(bad) }
            ex.message shouldContain "Bad initialization"
        }

        "let bindings should shadow outer bindings" {
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("x"))),
                value = B.pay(
                    P to B.letE(
                        "x", INT, B.n(10),
                        B.letE("x", INT, B.n(20), B.v("x"))
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }
    }

    "Type System - Function Calls" - {

        "should type check built-in functions" {
            // Based on TypeChecker.kt, only 'alldiff' and 'abs' are implemented
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("x"))),
                value = B.pay(
                    P to Call(B.v("abs"), listOf(B.m(P, "x") minus B.n(10)))
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "should reject unknown functions" {
            val bad = B.program(
                B.join(P),
                value = B.pay(
                    P to Call(B.v("unknown_function"), listOf(B.n(5)))
                )
            )
            shouldThrow<IllegalArgumentException> { typeCheck(bad) }
        }
    }

    "Built-ins - alldiff" - {

        "accepts alldiff over integers (constants and members)" {
            // constants only
            val pConst = B.program(
                B.join(P),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.n(1), B.n(2), B.n(3))),
                        B.n(100), B.n(0)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(pConst) }

            // role members
            val pFields = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("a"), B.i("b"), B.i("c"))),
                value = B.pay(
                    P to B.ite(
                        Call(
                            B.v("alldiff"),
                            listOf(B.m(P, "a"), B.m(P, "b"), B.m(P, "c"))
                        ),
                        B.n(100), B.n(0)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(pFields) }
        }

        "rejects alldiff with mixed or non-integer arguments" {
            // one boolean among ints
            val badMixed = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("x"), B.bl("b"))),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.m(P, "x"), B.n(5), B.m(P, "b"))),
                        B.n(1), B.n(0)
                    )
                )
            )
            shouldThrow<StaticError> { typeCheck(badMixed) }.message shouldContain "Incompatible operator argument"

            // booleans only
            val badBool = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.bl("p"), B.bl("q"))),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.m(P, "p"), B.m(P, "q"))),
                        B.n(1), B.n(0)
                    )
                )
            )
            shouldThrow<StaticError> { typeCheck(badBool) }.message shouldContain "Incompatible"
        }
    }


    "Type System - Complex GameIR Scenarios" - {

        "Monty Hall game type checking" {
            val types = mapOf(
                TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))
            )
            val p = B.program(
                types,
                B.join(Host, deposit = 100),
                B.join(Guest, deposit = 100),
                B.yieldTo(Host, listOf(B.dec("car", B.hidden(TypeId("door"))))),
                B.yieldTo(
                    Guest, listOf(B.dec("choice", TypeId("door")))
                ),
                B.yieldTo(
                    Host,
                    listOf(B.dec("goat", TypeId("door"))),
                    where = (B.m(Host, "goat") neq B.m(Guest, "choice")) and
                            (B.m(Host, "goat") neq B.m(Host, "car"))
                ),
                B.yieldTo(Guest, listOf(B.dec("switch", BOOL))),
                B.reveal(Host, listOf(B.dec("car", TypeId("door")))),
                value = Value(
                    mapOf(
                        Guest to B.ite(
                            (B.isDef(B.m(Host, "car")) and B.isDef(B.m(Guest, "switch"))),
                            B.ite(
                                (B.m(Guest, "choice") neq B.m(Host, "car")) iff B.m(Guest, "switch"),
                                B.n(20),
                                B.n(-20)
                            ),
                            B.n(-100)
                        ),
                        Host to B.ite(
                            (B.isDef(B.m(Host, "car")) and B.isDef(B.m(Guest, "switch"))),
                            B.n(0),
                            B.n(-100)
                        )
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "Prisoner's Dilemma type checking" {
            val p = B.program(
                B.join(Alice, deposit = 100),
                B.join(Bob, deposit = 100),
                B.yieldTo(Alice, listOf(B.dec("cooperate", BOOL))),
                B.yieldTo(Bob, listOf(B.dec("cooperate", BOOL))),
                value = Value(
                    mapOf(
                        Alice to B.ite(
                            B.m(Alice, "cooperate") and B.m(Bob, "cooperate"),
                            B.n(3),
                            B.ite(
                                B.m(Alice, "cooperate") and B.not(B.m(Bob, "cooperate")),
                                B.n(0),
                                B.ite(
                                    B.not(B.m(Alice, "cooperate")) and B.m(Bob, "cooperate"),
                                    B.n(5),
                                    B.n(1)
                                )
                            )
                        ),
                        Bob to B.ite(
                            B.m(Alice, "cooperate") and B.m(Bob, "cooperate"),
                            B.n(3),
                            B.ite(
                                B.not(B.m(Alice, "cooperate")) and B.m(Bob, "cooperate"),
                                B.n(0),
                                B.ite(
                                    B.m(Alice, "cooperate") and B.not(B.m(Bob, "cooperate")),
                                    B.n(5),
                                    B.n(1)
                                )
                            )
                        )
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "Multi-player lottery with many players" {
            val types = mapOf(
                TypeId("choice") to Subset(setOf(B.n(1), B.n(2), B.n(3), B.n(4), B.n(5)))
            )
            val p = B.program(
                types,
                B.join(P1, deposit = 50),
                B.join(P2, deposit = 50),
                B.join(P3, deposit = 50),
                B.yieldTo(P1, listOf(B.dec("c", TypeId("choice")))),
                B.yieldTo(P2, listOf(B.dec("c", TypeId("choice")))),
                B.yieldTo(P3, listOf(B.dec("c", TypeId("choice")))),
                value = Value(
                    mapOf(
                        P1 to B.ite(
                            (B.m(P1, "c") neq B.m(P2, "c")) and (B.m(P1, "c") neq B.m(P3, "c")),
                            B.n(150),
                            B.n(0)
                        ),
                        P2 to B.ite(
                            (B.m(P2, "c") neq B.m(P1, "c")) and (B.m(P2, "c") neq B.m(P3, "c")),
                            B.n(150),
                            B.n(0)
                        ),
                        P3 to B.ite(
                            (B.m(P3, "c") neq B.m(P1, "c")) and (B.m(P3, "c") neq B.m(P2, "c")),
                            B.n(150),
                            B.n(0)
                        )
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }
    }

    "Type System - Edge Cases and Error Messages" - {

        "empty games should be valid" {
            val p = B.program(value = Value(emptyMap()))
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "should provide helpful error messages" - {
            data class ErrorMessageCase(
                val prog: GameAst,
                val expectedKeywords: List<String>
            )

            withData(
                ErrorMessageCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.bl("x"))),
                        value = B.pay(P to (B.m(P, "x") plus B.n(1)))
                    ),
                    listOf("bool", "int", "Incompatible")
                ),
                ErrorMessageCase(
                    B.program(
                        B.yieldTo(role("UnknownRole"), listOf(B.i("x")))
                    ),
                    listOf("UnknownRole is not a role")
                ),
                ErrorMessageCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.bl("x"))),
                        B.reveal(P, listOf(B.dec("x", INT))) // must be hidden
                    ),
                    listOf("must be hidden")
                ),
                ErrorMessageCase(
                    B.program(
                        B.join(P),
                        value = B.pay(P to B.m(P, "undefined"))
                    ),
                    listOf("undefined")
                ),
                ErrorMessageCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.i("x")), where = B.m(P, "x"))
                    ),
                    listOf("Where clause failed")
                )
            ) { case ->
                val ex = shouldThrow<StaticError> { typeCheck(case.prog) }
                case.expectedKeywords.forEach { keyword ->
                    ex.message shouldContain keyword
                }
            }
        }

        "should handle deeply nested expressions" {
            val nested = B.ite(
                B.m(P, "a") gt B.n(0),
                B.ite(
                    B.m(P, "b") gt B.n(0),
                    B.ite(
                        B.m(P, "c") gt B.n(0),
                        B.ite(B.m(P, "d") gt B.n(0), B.n(1000), B.n(100)),
                        B.n(10)
                    ),
                    B.n(1)
                ),
                B.n(0)
            )
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.i("a"), B.i("b"), B.i("c"), B.i("d"))),
                value = B.pay(P to nested)
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }

        "should handle complex boolean expressions" {
            val complex = (B.m(P, "a") and B.m(P, "b")) or
                    (B.not(B.m(P, "c")) and (B.m(P, "a") iff B.m(P, "b")))
            val p = B.program(
                B.join(P),
                B.yieldTo(P, listOf(B.bl("a"), B.bl("b"), B.bl("c"))),
                value = B.pay(P to B.ite(complex, B.n(100), B.n(0)))
            )
            shouldNotThrow<StaticError> { typeCheck(p) }
        }
    }
})
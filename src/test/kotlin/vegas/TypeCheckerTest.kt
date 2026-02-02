package vegas

import io.kotest.assertions.throwables.shouldNotThrow
import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.datatest.withData
import io.kotest.matchers.string.shouldContain

import vegas.frontend.Exp
import vegas.frontend.Exp.*
import vegas.frontend.GameAst
import vegas.frontend.Ext
import vegas.frontend.Kind
import vegas.frontend.Outcome
import vegas.frontend.Outcome.*
import vegas.frontend.Query
import vegas.frontend.Role
import vegas.frontend.TypeExp
import vegas.frontend.TypeExp.*
import vegas.frontend.VarDec

// -------- Test-local builders --------
private object B {
    // literals
    fun n(i: Int) = Const.Num(i)
    fun b(v: Boolean) = Const.Bool(v)

    // variables / members
    fun v(name: String) = Var(VarId(name))
    fun m(owner: Role, field: String) = Field(FieldRef(owner.id, VarId(field)))

    fun not(e: Exp) = UnOp("!", e)
    fun isDef(e: Exp) = UnOp("isDefined", e)
    fun isUndef(e: Exp) = UnOp("isUndefined", e)

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

    // queries and binds
    private fun q(role: Role, params: List<VarDec> = emptyList(), deposit: Int = 0, where: Exp = b(true), handler: Outcome? = null) =
        Query(role = role, params = params, deposit = n(deposit), where = where, handler = handler)

    fun join(role: Role, params: List<VarDec> = emptyList(), deposit: Int = 0, where: Exp = b(true)) =
        Ext.Bind(Kind.JOIN, listOf(q(role, params, deposit, where)), null, Ext.Value(Value(emptyMap())))

    fun yieldTo(role: Role, params: List<VarDec>, where: Exp = b(true), handler: Outcome? = null) =
        Ext.Bind(Kind.YIELD, listOf(q(role, params, 0, where, handler)), null, Ext.Value(Value(emptyMap())))

    fun commitTo(role: Role, params: List<VarDec>, where: Exp = b(true), handler: Outcome? = null) =
        Ext.Bind(Kind.COMMIT, listOf(q(role, params, 0, where, handler)), null, Ext.Value(Value(emptyMap())))

    fun reveal(role: Role, params: List<VarDec>, where: Exp = b(true), handler: Outcome? = null) =
        Ext.Bind(Kind.REVEAL, listOf(q(role, params, 0, where, handler)), null, Ext.Value(Value(emptyMap())))

    // payouts
    fun pay(vararg outs: Pair<Role, Exp>) = Value(mapOf(*outs))

    /**
     * Program builder per request:
     *  program(types, binds..., value?)
     *
     * Threads binds left->right and attaches an optional final Outcome.
     */
    fun program(
        types: Map<TypeId, TypeExp>,
        vararg binds: Ext,
        value: Outcome? = null,
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
        return GameAst(name, desc = "", types = types, macros = emptyList(), game = game)
    }

    fun program(
        vararg binds: Ext,
        value: Outcome? = null,
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

            withData(nameFn = { it.toString() },
                ValidCase(
                    B.program(B.join(P, params = listOf(B.i("x")))),
                    "integer parameter"
                ),
                ValidCase(
                    B.program(B.join(P, params = listOf(B.bl("b")))),
                    "boolean parameter"
                ),
                ValidCase(
                    B.program(B.join(P, params = listOf(B.i("x"), B.bl("b")))),
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
                        B.join(P, params = listOf(B.i("x"))),
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

            withData(nameFn = { it.toString() },
                TypeMismatchCase(
                    B.program(
                        B.join(P, params = listOf(B.i("x"))),
                        value = B.pay(P to (B.m(P, "x") and B.b(true)))
                    ),
                    "Logic operator"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P, params = listOf(B.bl("b"))),
                        value = B.pay(P to (B.m(P, "b") plus B.n(1)))
                    ),
                    "Arithmetic operator"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P, params = listOf(B.i("x"))),
                        value = B.pay(
                            P to B.ite(
                                B.m(P, "x") gt B.b(true),  // int > bool -> error
                                B.n(1),
                                B.n(0)
                            )
                        )
                    ),
                    "Comparison operator"
                ),
                TypeMismatchCase(
                    B.program(
                        B.join(P),
                        value = B.pay(P to B.b(true))  // outcome must be int
                    ),
                    "Outcome value must be int"
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
            withData(nameFn = { it.toString() },
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
                    B.join(P, params = listOf(B.dec("flip", TypeId("coin"))))
                ),
                // type small, big sets; yield both
                B.program(
                    types = mapOf(
                        TypeId("small") to Subset(setOf(B.n(1), B.n(2), B.n(3))),
                        TypeId("big") to Subset(setOf(B.n(10), B.n(11), B.n(12)))
                    ),
                    B.join(P, params = listOf(B.dec("s", TypeId("small")), B.dec("b", TypeId("big"))))
                )
            ) { prog ->
                shouldNotThrow<StaticError> { typeCheck(prog) }
            }
        }

        "should handle range types correctly" - {
            withData(nameFn = { it.toString() },
                B.program(
                    types = mapOf(TypeId("digit") to Range(B.n(0), B.n(9))),
                    B.join(P, params = listOf(B.dec("d", TypeId("digit"))))
                ),
                B.program(
                    types = mapOf(TypeId("percent") to Range(B.n(0), B.n(100))),
                    B.join(P, params = listOf(B.dec("p", TypeId("percent"))))
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
                        B.join(P, params = listOf(B.dec("d", TypeId("door"))),
                            where = B.m(P, "d") neq B.n(1))
                    ),
                    B.program(
                        types = mapOf(TypeId("coin") to Subset(setOf(B.n(0), B.n(1)))),
                        B.join(P, params = listOf(B.dec("c", TypeId("coin"))),
                            where = (B.m(P, "c") eq B.n(0)) or (B.m(P, "c") eq B.n(1)))
                    ),
                    B.program(
                        types = mapOf(TypeId("range") to Range(B.n(1), B.n(10))),
                        B.join(P, params = listOf(B.dec("r", TypeId("range"))),
                            where = B.m(P, "r") gt B.n(5))
                    )
                )
                validCases.forEach { program ->
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "rejects invalid where constraints" {
                val bad = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.i("x")), where = B.m(P, "x")) // non-boolean where
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "Where clause must be bool"
            }
        }
    }

    "Type System - Hidden Types (via commit)" - {

        "should handle commit declarations (creates hidden fields)" - {
            withData(nameFn = { it.toString() },
                // join H(); commit H(secret: int); reveal H(secret: int)
                B.program(
                    B.join(H),
                    B.commitTo(H, listOf(B.i("secret"))),
                    B.reveal(H, listOf(B.i("secret")))
                ),
                // type door = {0,1,2}; join H(); commit H(car: door); reveal H(car: door)
                B.program(
                    types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                    B.join(H),
                    B.commitTo(H, listOf(B.dec("car", TypeId("door")))),
                    B.reveal(H, listOf(B.dec("car", TypeId("door"))))
                ),
                // join H(); commit H(x: int); yield H(y: int); reveal H(x: int)
                B.program(
                    B.join(H),
                    B.commitTo(H, listOf(B.i("x"))),
                    B.yieldTo(H, listOf(B.i("y"))),
                    B.reveal(H, listOf(B.i("x")))
                ),
                // join H(); commit H(a: bool, b: bool); reveal H(a: bool, b: bool)
                B.program(
                    B.join(H),
                    B.commitTo(H, listOf(B.bl("a"), B.bl("b"))),
                    B.reveal(H, listOf(B.bl("a"), B.bl("b")))
                )
            ) { prog ->
                shouldNotThrow<StaticError> { typeCheck(prog) }
            }
        }

        "should reject commits without corresponding reveals" {
            val bad = B.program(
                B.join(H),
                B.commitTo(H, listOf(B.i("secret")))
                // missing: B.reveal(H, listOf(B.i("secret")))
            )
            val exception = shouldThrow<StaticError> { typeCheck(bad) }
            exception.message shouldContain "no corresponding reveal"
        }

        "should validate reveal operations" - {

            "accepts revealing committed values" {
                val validReveals = listOf(
                    // join H(); commit H(s: int); reveal H(s: int)
                    B.program(
                        B.join(H),
                        B.commitTo(H, listOf(B.i("s"))),
                        B.reveal(H, listOf(B.i("s")))
                    ),
                    // type door = {0,1,2}; join H(); commit H(car: door); reveal H(car: door)
                    B.program(
                        types = mapOf(TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))),
                        B.join(H),
                        B.commitTo(H, listOf(B.dec("car", TypeId("door")))),
                        B.reveal(H, listOf(B.dec("car", TypeId("door"))))
                    ),
                    // join H(); commit H(a: int, b: bool); reveal H(a: int, b: bool)
                    B.program(
                        B.join(H),
                        B.commitTo(H, listOf(B.i("a"), B.bl("b"))),
                        B.reveal(H, listOf(B.i("a"), B.bl("b")))
                    )
                )
                validReveals.forEach { program ->
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "rejects revealing non-committed values" {
                val bad = B.program(
                    B.join(H),
                    B.yieldTo(H, listOf(B.i("public"))),
                    B.reveal(H, listOf(B.i("public")))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "must be hidden"
            }

            "rejects type mismatches in reveal" {
                val bad = B.program(
                    B.join(H),
                    B.commitTo(H, listOf(B.i("s"))),
                    B.reveal(H, listOf(B.bl("s"))) // mismatch: int vs bool
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                // just assert that an error message was produced (type mismatch)
                exception.message shouldContain "Reveal type mismatch for 'H.s': expected int, got bool"
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
                val program = B.program(
                    B.join(P, params = listOf(B.i("x"), B.bl("y"))),
                    value = B.pay(P to B.ite(B.m(P, "x") eq B.n(5), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(program) }
            }

            "rejects accessing undefined roles" {
                val bad = B.program(
                    B.yieldTo(role("UnknownRole"), listOf(B.i("x")))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "UnknownRole is not a role"
            }

            "rejects accessing undefined members" {
                val bad = B.program(
                    B.join(P),
                    value = B.pay(P to B.m(P, "undefined"))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "undefined"
            }
        }

        "should handle role scoping correctly" - {

            "member access requires role in scope" {
                val bad = B.program(
                    B.join(P),
                    B.yieldTo(Q, listOf(B.i("x"))), // Q never joined
                    value = B.pay(P to B.m(Q, "x"))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "Q is not a role"
            }

            "cross-role member access in multi-player games" {
                val program = B.program(
                    B.join(P1), B.join(P2),
                    B.yieldTo(P1, listOf(B.i("x")), handler = B.pay(P2 to B.n(100))),
                    B.yieldTo(P2, listOf(B.i("y")), handler = B.pay(P1 to B.n(100))),
                    value = Value(
                        mapOf(
                            P1 to B.ite(B.m(P2, "y") gt B.m(P1, "x"), B.n(100), B.n(0)),
                            P2 to B.ite(B.m(P1, "x") gt B.m(P2, "y"), B.n(100), B.n(0))
                        )
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(program) }
            }
        }
    }
    "Type System - Operators" - {

        "arithmetic operators require integers" - {
            data class ArithmeticCase(val expr: Exp, val valid: Boolean)

            withData(nameFn = { it.toString() },
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
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(cmp, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "reject non-integer comparisons" {
                val invalid = listOf(
                    B.b(true) lt B.b(false),
                    B.n(5) gt B.b(true),
                    B.b(false) lte B.n(3)
                )
                invalid.forEach { cmp ->
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(cmp, B.n(1), B.n(0)))
                    )
                    shouldThrow<StaticError> { typeCheck(program) }
                }
            }
        }

        "boolean operators require booleans" - {

            "accept valid boolean operations" {
                val valid = listOf(
                    B.b(true) and B.b(false),
                    B.b(true) or B.b(false),
                    B.not(B.b(true)),
                    B.not(B.b(true) and B.b(false))
                )
                valid.forEach { bexpr ->
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(bexpr, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "reject invalid boolean operations" {
                val invalid = listOf(
                    B.n(5) and B.b(true),
                    B.b(false) or B.n(3),
                    B.not(B.n(42))
                )
                invalid.forEach { bexpr ->
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(bexpr, B.n(1), B.n(0)))
                    )
                    val exception = shouldThrow<StaticError> { typeCheck(program) }
                    exception.message shouldContain "expects"
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
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to B.ite(eqexpr, B.n(1), B.n(0)))
                    )
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "special iff operators (<->, <-!->)" {
                val program1 = B.program(
                    B.join(P, params = listOf(B.bl("a"), B.bl("b"))),
                    value = B.pay(P to B.ite(B.m(P, "a") iff B.m(P, "b"), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(program1) }

                val program2 = B.program(
                    B.join(P, params = listOf(B.bl("a"), B.bl("b"))),
                    value = B.pay(P to B.ite(B.m(P, "a") xnor B.m(P, "b"), B.n(100), B.n(0)))
                )
                shouldNotThrow<StaticError> { typeCheck(program2) }
            }
        }

        "null checking operators" - {

            "isDefined and isUndefined" {
                // With new semantics: || null handler makes fields nullable, enabling isDefined/isUndefined
                val program1 = B.program(
                    B.join(P), B.join(Q),
                    B.yieldTo(P, listOf(B.i("x")), handler = Null), // || null makes x optional
                    value = Value(
                        mapOf(
                            P to B.ite(B.isDef(B.m(P, "x")), B.n(100), B.n(0)), // int on both branches
                            Q to B.ite(B.isDef(B.m(P, "x")), B.n(0), B.n(100))
                        )
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(program1) }

                // Cannot return P.opt (opt(int)) as an int payout without an explicit unwrap/default.
                val program2a = B.program(
                    B.join(P),
                    B.yieldTo(P, listOf(B.i("opt")), handler = Null), // || null
                    value = B.pay(
                        P to B.ite(B.isUndef(B.m(P, "opt")), B.n(-100), B.n(0)) // both int
                    )
                )
                shouldNotThrow<StaticError> { typeCheck(program2a) }
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
                    val program = B.program(
                        B.join(P),
                        value = B.pay(P to expr)
                    )
                    shouldNotThrow<StaticError> { typeCheck(program) }
                }
            }

            "rejects non-boolean conditions" {
                val bad = B.program(
                    B.join(P),
                    value = B.pay(P to B.ite(B.n(5), B.n(10), B.n(20)))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                exception.message shouldContain "Condition must be bool, found"
            }

            "reject non-numerical outcome" {
                val types = mapOf(
                    TypeId("big") to Subset(setOf(B.n(10), B.n(11), B.n(12)))
                )
                val bad = B.program(
                    types,
                    B.join(P, params = listOf(B.bl("b"), B.dec("s", BOOL), B.dec("g", TypeId("big")))),
                    value = B.pay(P to B.ite(B.m(P, "b"), B.m(P, "s"), B.m(P, "g")))
                )
                val exception = shouldThrow<StaticError> { typeCheck(bad) }
                // This should fail because the outcome must be int, but we're returning bool or big (subset of int)
                // Error could be about conditional branches being incompatible or outcome not being int
                val hasError = exception.message!!.contains("Conditional branches are incompatible") ||
                               exception.message!!.contains("Outcome value must be an int") ||
                               exception.message!!.contains("actual: bool")
                if (!hasError) {
                    throw AssertionError("Expected error about incompatible types or non-int outcome, got: ${exception.message}")
                }
            }
        }

        "should handle nested conditionals" {
            val nested = B.ite(
                B.m(P, "x") gt B.n(10),
                B.ite(B.m(P, "y") gt B.n(5), B.n(100), B.n(50)),
                B.ite(B.m(P, "y") gt B.n(5), B.n(25), B.n(0))
            )
            val program = B.program(
                B.join(P, params = listOf(B.i("x"), B.i("y"))),
                value = B.pay(P to nested)
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }
    }

    "Type System - Let Expressions" - {

        "should handle let bindings in expressions" {
            val program = B.program(
                B.join(P, params = listOf(B.i("x"))),
                value = B.pay(
                    P to B.letE(
                        "y", INT,
                        B.m(P, "x") plus B.n(10),
                        B.v("y") times B.n(2)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "should handle let bindings in outcomes" {
            val program = B.program(
                B.join(P), B.join(Q),
                B.yieldTo(P, listOf(B.i("x")), handler = B.pay(Q to B.n(100))),
                value = B.letO(
                    "total", INT,
                    B.m(P, "x") times B.n(100),
                    Value(
                        mapOf(
                            P to B.v("total"),
                            Q to BinOp("-", B.n(0), B.v("total"))
                        )
                    )
                ) // No need to call desugar - ToIR.desugarOutcome handles this
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "should reject type mismatches in let initialization" {
            val bad = B.program(
                B.join(P),
                value = B.pay(
                    P to B.letE("x", INT, B.b(true), B.v("x") plus B.n(5))
                )
            )
            val exception = shouldThrow<StaticError> { typeCheck(bad) }
            exception.message shouldContain "Bad let initialization"
        }

        "let bindings should shadow outer bindings" {
            val program = B.program(
                B.join(P, params = listOf(B.i("x"))),
                value = B.pay(
                    P to B.letE(
                        "x", INT, B.n(10),
                        B.letE("x", INT, B.n(20), B.v("x"))
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }
    }

    "Type System - Function Calls" - {

        "should type check built-in functions" {
            // Based on TypeChecker.kt, only 'alldiff' and 'abs' are implemented
            val program = B.program(
                B.join(P, params = listOf(B.i("x"))),
                value = B.pay(
                    P to Call(B.v("abs"), listOf(B.m(P, "x") minus B.n(10)))
                )
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "should reject unknown functions" {
            val bad = B.program(
                B.join(P),
                value = B.pay(
                    P to Call(B.v("unknown_function"), listOf(B.n(5)))
                )
            )
            shouldThrow<StaticError> { typeCheck(bad) }
        }
    }

    "Built-ins - alldiff" - {

        "accepts alldiff over integers (constants and members)" {
            // constants only
            val programConst = B.program(
                B.join(P),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.n(1), B.n(2), B.n(3))),
                        B.n(100), B.n(0)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(programConst) }

            // role members
            val programFields = B.program(
                B.join(P, params = listOf(B.i("a"), B.i("b"), B.i("c"))),
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
            shouldNotThrow<StaticError> { typeCheck(programFields) }
        }

        "rejects alldiff with mixed or non-integer arguments" {
            // one boolean among ints
            val badMixed = B.program(
                B.join(P, params = listOf(B.i("x"), B.bl("b"))),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.m(P, "x"), B.n(5), B.m(P, "b"))),
                        B.n(1), B.n(0)
                    )
                )
            )
            shouldThrow<StaticError> { typeCheck(badMixed) }.message shouldContain "alldiff"

            // booleans only
            val badBool = B.program(
                B.join(P, params = listOf(B.bl("p"), B.bl("q"))),
                value = B.pay(
                    P to B.ite(
                        Call(B.v("alldiff"), listOf(B.m(P, "p"), B.m(P, "q"))),
                        B.n(1), B.n(0)
                    )
                )
            )
            shouldThrow<StaticError> { typeCheck(badBool) }.message shouldContain "alldiff"
        }
    }


    "Type System - Complex GameIR Scenarios" - {

        "Monty Hall game type checking" {
            val types = mapOf(
                TypeId("door") to Subset(setOf(B.n(0), B.n(1), B.n(2)))
            )
            val program = B.program(
                types,
                B.join(Host, deposit = 100),
                B.join(Guest, deposit = 100),
                B.commitTo(Host, listOf(B.dec("car", TypeId("door"))), handler = B.pay(Guest to B.n(200))),
                B.yieldTo(
                    Guest, listOf(B.dec("choice", TypeId("door"))),
                    handler = B.pay(Host to B.n(200))
                ),
                B.yieldTo(
                    Host,
                    listOf(B.dec("goat", TypeId("door"))),
                    where = B.m(Host, "goat") neq B.m(Guest, "choice"),
                    handler = B.pay(Guest to B.n(200))
                ),
                B.yieldTo(Guest, listOf(B.dec("switch", BOOL)), handler = B.pay(Host to B.n(200))),
                B.reveal(
                    Host,
                    listOf(B.dec("car", TypeId("door"))),
                    where = B.m(Host, "goat") neq B.m(Host, "car")
                ),
                value = Value(
                    mapOf(
                        Guest to B.ite(
                            (B.m(Guest, "choice") neq B.m(Host, "car")) iff B.m(Guest, "switch"),
                            B.n(20),
                            B.n(-20)
                        ),
                        Host to B.n(0)
                    )
                )
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "Prisoner's Dilemma type checking" {
            val program = B.program(
                B.join(Alice, deposit = 100),
                B.join(Bob, deposit = 100),
                B.yieldTo(Alice, listOf(B.dec("cooperate", BOOL)), handler = B.pay(Bob to B.n(200))),
                B.yieldTo(Bob, listOf(B.dec("cooperate", BOOL)), handler = B.pay(Alice to B.n(200))),
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
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "Multi-player lottery with many players" {
            val types = mapOf(
                TypeId("choice") to Subset(setOf(B.n(1), B.n(2), B.n(3), B.n(4), B.n(5)))
            )
            val program = B.program(
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
            shouldNotThrow<StaticError> { typeCheck(program) }
        }
    }

    "Type System - Edge Cases and Error Messages" - {

        "empty games should be valid" {
            val program = B.program(value = Value(emptyMap()))
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "should provide helpful error messages" - {
            data class ErrorMessageCase(
                val prog: GameAst,
                val expectedKeywords: List<String>
            )

            withData(nameFn = { it.toString() },
                ErrorMessageCase(
                    B.program(
                        B.join(P),
                        B.yieldTo(P, listOf(B.bl("x"))),
                        value = B.pay(P to (B.m(P, "x") plus B.n(1)))
                    ),
                    listOf("bool", "int", "Arithmetic operator")
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
                    listOf("Where clause must be bool")
                )
            ) { case ->
                val exception = shouldThrow<StaticError> { typeCheck(case.prog) }
                case.expectedKeywords.forEach { keyword ->
                    exception.message shouldContain keyword
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
            val program = B.program(
                B.join(P, params = listOf(B.i("a"), B.i("b"), B.i("c"), B.i("d"))),
                value = B.pay(P to nested)
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }

        "should handle complex boolean expressions" {
            val complex = (B.m(P, "a") and B.m(P, "b")) or
                    (B.not(B.m(P, "c")) and (B.m(P, "a") iff B.m(P, "b")))
            val program = B.program(
                B.join(P, params = listOf(B.bl("a"), B.bl("b"), B.bl("c"))),
                value = B.pay(P to B.ite(complex, B.n(100), B.n(0)))
            )
            shouldNotThrow<StaticError> { typeCheck(program) }
        }
    }
})
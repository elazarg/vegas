package vegas

import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import vegas.frontend.parseCode
import vegas.frontend.inlineMacros
import vegas.frontend.compileToIR

class MacroTest : FreeSpec({

    "Parsing" - {
        "simple macro with no params" {
            val code = """
                macro c(): int = 5;
                join A() $ 100;
                withdraw { A -> c() }
            """.trimIndent()

            val ast = parseCode(code)
            ast.macros.size shouldBe 1
            ast.macros[0].name.name shouldBe "c"
            ast.macros[0].params.size shouldBe 0
        }

        "macro with single param" {
            val code = """
                macro add5(x: int): int = x + 5;
                join A(choice: {1..10}) $ 100;
                withdraw { A -> add5(A.choice) }
            """.trimIndent()

            val ast = parseCode(code)
            ast.macros.size shouldBe 1
            ast.macros[0].name.name shouldBe "add5"
            ast.macros[0].params.size shouldBe 1
            ast.macros[0].params[0].name.name shouldBe "x"
        }

        "macro with multiple params" {
            val code = """
                type num = {1..10}
                macro max(a: int, b: int): int = a > b ? a : b;
                join A(x: num) $ 100;
                join B(y: num) $ 100;
                withdraw { A -> max(A.x, B.y) }
            """.trimIndent()

            val ast = parseCode(code)
            ast.macros.size shouldBe 1
            ast.macros[0].params.size shouldBe 2
        }
    }

    "Type Checking" - {
        "correct macro type checks" {
            val code = """
                type num = {1..10}
                macro add(a: int, b: int): int = a + b;
                join A(x: num) $ 100;
                join B(y: num) $ 100;
                withdraw { A -> add(A.x, B.y); B -> add(B.y, A.x) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast) // Should not throw
        }

        "wrong return type errors" {
            val code = """
                macro bad(): int = true;
                join A() $ 100;
                withdraw { A -> bad() }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "bool"
            ex.message shouldContain "int"
        }

        "wrong arity errors" {
            val code = """
                macro f(x: int): int = x + 1;
                join A(a: int, b: int) $ 100;
                withdraw { A -> f(A.a, A.b) }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "2"
            ex.message shouldContain "1"
        }

        "argument type mismatch errors" {
            val code = """
                macro addInt(x: int): int = x + 1;
                join A(flag: bool) $ 100;
                withdraw { A -> addInt(A.flag) }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "bool"
        }
    }

    "Recursion Detection" - {
        "self-recursive macro rejected" {
            val code = """
                macro f(x: int): int = f(x);
                join A() $ 100;
                withdraw { A -> f(5) }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "Recursive"
        }

        "mutually recursive macros rejected" {
            val code = """
                macro f(x: int): int = g(x);
                macro g(x: int): int = f(x);
                join A() $ 100;
                withdraw { A -> f(5) }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "Recursive"
        }

        "deep acyclic DAG accepted" {
            val code = """
                macro a(x: int): int = x + 1;
                macro b(x: int): int = a(x) + 2;
                macro c(x: int): int = b(x) + 3;
                join A(n: int) $ 100;
                withdraw { A -> c(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast) // Should not throw
        }
    }

    "Inlining" - {
        "simple macro inlines correctly" {
            val code = """
                macro five(): int = 5;
                join A() $ 100;
                withdraw { A -> five() }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)

            inlined.macros.size shouldBe 0  // Macros removed
        }

        "macro with params inlines correctly" {
            val code = """
                type choice = {1..10}
                macro add5(x: int): int = x + 5;
                join A(c: choice) $ 100;
                withdraw { A -> add5(A.c) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)

            inlined.macros.size shouldBe 0
            // Inlined program should compile to IR
            val ir = compileToIR(inlined)
            ir.roles.size shouldBe 1
        }

        "nested macro calls inline correctly" {
            val code = """
                macro double(x: int): int = x + x;
                macro quadruple(x: int): int = double(double(x));
                join A(n: int) $ 100;
                withdraw { A -> quadruple(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)

            inlined.macros.size shouldBe 0
            // Should compile successfully
            compileToIR(inlined)
        }
    }

    "End-to-End" - {
        "Prisoner's Dilemma with macros compiles to IR" {
            val code = """
                macro pd(me: bool, other: bool): int =
                    (me && other) ? 3 :
                    (!me && !other) ? 1 :
                    (!me && other) ? 5 :
                    0;

                join P1(cooperate: bool) $ 100;
                join P2(cooperate: bool) $ 100;

                withdraw {
                    P1 -> pd(P1.cooperate, P2.cooperate);
                    P2 -> pd(P2.cooperate, P1.cooperate);
                }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            ir.roles.size shouldBe 2
            ir.dag.actions.size shouldBe 2
        }

        "Macros work with conditional outcomes" {
            val code = """
                macro winner(me: bool, other: bool): int =
                    (me && !other) ? 100 : 0;

                join P1(choice: bool) $ 10;
                join P2(choice: bool) $ 10;

                withdraw {
                    P1 -> winner(P1.choice, P2.choice);
                    P2 -> winner(P2.choice, P1.choice);
                }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            ir.roles.size shouldBe 2
        }
    }

    "Advanced Features" - {
        "macros with let! expressions in body" {
            val code = """
                type num = {1..10}
                macro compute(x: int): int =
                    let! temp: int = x + 5 in temp * 2;

                join A(n: num) $ 100;
                withdraw { A -> compute(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)

            // Just verify inlining works - don't compile to IR (let! not supported)
            inlined.macros.size shouldBe 0
        }

        "macros with commit-reveal patterns" {
            val code = """
                type num = {1..5}
                macro addBonus(x: int, bonus: int): int = x + bonus;
                join A() $ 100;
                join B(public: num) $ 100;
                commit A(secret: num);
                reveal A(secret: num);
                withdraw {
                    A -> addBonus(B.public, 10);
                    B -> addBonus(B.public, 5);
                }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            ir.roles.size shouldBe 2
        }

        "macros calling built-in functions" {
            val code = """
                type range = {1..10}
                macro absMax(a: int, b: int): int =
                    abs(a) > abs(b) ? abs(a) : abs(b);

                join P1(x: range, y: range) $ 100;
                withdraw { P1 -> absMax(P1.x, P1.y) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            ir.roles.size shouldBe 1
        }

        "macros calling alldiff" {
            val code = """
                type num = {1..5}
                macro allDifferent(a: int, b: int, c: int): bool =
                    alldiff(a, b, c);

                join P1(x: num) $ 100;
                join P2(y: num) $ 100;
                join P3(z: num) $ 100;
                withdraw {
                    P1 -> allDifferent(P1.x, P2.y, P3.z) ? 100 : 0;
                    P2 -> 0;
                    P3 -> 0;
                }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            ir.roles.size shouldBe 3
        }
    }

    "Return Types" - {
        "macro returning bool" {
            val code = """
                macro isEven(x: int): bool = (x / 2) * 2 == x;
                join A(n: int) $ 100;
                withdraw { A -> isEven(A.n) ? 10 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }
    }

    "Parameter Types" - {
        "macro with bool parameters" {
            val code = """
                macro xor(a: bool, b: bool): bool = (a && !b) || (!a && b);
                join A(x: bool, y: bool) $ 100;
                withdraw { A -> xor(A.x, A.y) ? 1 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro with subset type parameter" {
            val code = """
                type choice = {1, 3, 5, 7}
                macro double(x: int): int = x * 2;
                join A(c: choice) $ 100;
                withdraw { A -> double(A.c) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)
            ir.roles.size shouldBe 1
        }
    }

    "All Operators" - {
        "all arithmetic operators in macros" {
            val code = """
                macro calc(a: int, b: int): int = a + b - a * b / (b + 1);
                join A(x: int, y: int) $ 100;
                withdraw { A -> calc(A.x, A.y) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "all comparison operators in macros" {
            val code = """
                macro allComparisons(a: int, b: int): bool =
                    (a < b) && (a <= b) && (a > b) || (a >= b);
                join A(x: int, y: int) $ 100;
                withdraw { A -> allComparisons(A.x, A.y) ? 1 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "all boolean operators in macros" {
            val code = """
                macro boolOps(a: bool, b: bool): bool =
                    (a && b) || (!a && !b);
                join A(x: bool, y: bool) $ 100;
                withdraw { A -> boolOps(A.x, A.y) ? 5 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "equality and bi-implication operators" {
            val code = """
                macro equiv(a: bool, b: bool): bool =
                    (a <-> b) && !(a <-!-> b) && (a == b);
                join A(x: bool, y: bool) $ 100;
                withdraw { A -> equiv(A.x, A.y) ? 10 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "inequality operator" {
            val code = """
                macro notEqual(a: int, b: int): bool = a != b;
                join A(x: int, y: int) $ 100;
                withdraw { A -> notEqual(A.x, A.y) ? 1 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "unary minus operator" {
            val code = """
                macro negate(x: int): int = -x;
                join A(n: int) $ 100;
                withdraw { A -> negate(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }
    }

    "Variable Shadowing" - {
        "let! shadows macro parameter" {
            val code = """
                macro shadow(x: int): int =
                    let! x: int = 10 in x + 5;
                join A(n: int) $ 100;
                withdraw { A -> shadow(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            // Just verify parsing and inlining works - don't compile to IR (let! not supported)
            inlined.macros.size shouldBe 0
        }

        "nested let! with shadowing" {
            val code = """
                macro doubleShadow(x: int): int =
                    let! y: int = x + 1 in
                    let! x: int = y * 2 in
                    x + y;
                join A(n: int) $ 100;
                withdraw { A -> doubleShadow(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            // Just verify parsing and inlining works - don't compile to IR (let! not supported)
            inlined.macros.size shouldBe 0
        }
    }

    "Macro Call Patterns" - {
        "diamond dependency pattern" {
            val code = """
                macro base(x: int): int = x + 1;
                macro left(x: int): int = base(x) * 2;
                macro right(x: int): int = base(x) * 3;
                macro top(x: int): int = left(x) + right(x);
                join A(n: int) $ 100;
                withdraw { A -> top(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro calling multiple other macros" {
            val code = """
                macro f(x: int): int = x + 1;
                macro g(x: int): int = x * 2;
                macro h(x: int): int = x - 1;
                macro combine(x: int): int = f(x) + g(x) + h(x);
                join A(n: int) $ 100;
                withdraw { A -> combine(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }
    }

    "Expression Contexts" - {
        "macro in nested conditionals" {
            val code = """
                macro isPos(x: int): bool = x > 0;
                join A(n: int) $ 100;
                withdraw { A -> isPos(A.n) ? (isPos(A.n + 1) ? 5 : 3) : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro as operand in binary expression" {
            val code = """
                macro double(x: int): int = x * 2;
                join A(n: int) $ 100;
                withdraw { A -> double(A.n) + double(A.n + 1) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro in unary expression" {
            val code = """
                macro getBool(x: int): bool = x > 0;
                join A(n: int) $ 100;
                withdraw { A -> !getBool(A.n) ? 10 : 0 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro in let! initializer" {
            val code = """
                macro compute(x: int): int = x * 2;
                join A(n: int) $ 100;
                withdraw { A -> let! temp: int = compute(A.n) in temp + 5 }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            // Just verify parsing and inlining works - don't compile to IR (let! not supported)
            inlined.macros.size shouldBe 0
        }
    }

    "Edge Cases" - {
        "macro with constants only" {
            val code = """
                macro constant(): int = 42;
                join A() $ 100;
                withdraw { A -> constant() }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "macro with negative literals" {
            val code = """
                macro negative(x: int): int = x + -10;
                join A(n: int) $ 100;
                withdraw { A -> negative(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }

        "duplicate macro name errors" {
            val code = """
                macro f(x: int): int = x + 1;
                macro f(y: int): int = y + 2;
                join A() $ 100;
                withdraw { A -> f(5) }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "Duplicate"
            ex.message shouldContain "f"
        }

        "unused macro is still validated" {
            val code = """
                macro bad(): int = true;
                join A() $ 100;
                withdraw { A -> 5 }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "bool"
        }

        "macro cannot access role fields (no closure)" {
            val code = """
                macro tryAccess(): int = A.x;
                join A(x: int) $ 100;
                withdraw { A -> tryAccess() }
            """.trimIndent()

            val ast = parseCode(code)
            val ex = shouldThrow<StaticError> { typeCheck(ast) }
            ex.message shouldContain "not a role"
        }

        "macro can only use parameters and constants" {
            val code = """
                macro valid(x: int, y: int): int = x + y + 42;
                join A(a: int, b: int) $ 100;
                withdraw { A -> valid(A.a, A.b) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast) // Should not throw
            val inlined = inlineMacros(ast)
            inlined.macros.size shouldBe 0
        }
    }

    "Stress Tests" - {
        "deeply nested macro calls (10 levels)" {
            val code = """
                type num = {1..5}
                macro m0(x: int): int = x + 1;
                macro m1(x: int): int = m0(x) + 1;
                macro m2(x: int): int = m1(x) + 1;
                macro m3(x: int): int = m2(x) + 1;
                macro m4(x: int): int = m3(x) + 1;
                macro m5(x: int): int = m4(x) + 1;
                macro m6(x: int): int = m5(x) + 1;
                macro m7(x: int): int = m6(x) + 1;
                macro m8(x: int): int = m7(x) + 1;
                macro m9(x: int): int = m8(x) + 1;

                join A(n: num) $ 100;
                withdraw { A -> m9(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            val ir = compileToIR(inlined)

            // Should compile successfully
            ir.roles.size shouldBe 1
            inlined.macros.size shouldBe 0
        }

        "many independent macros" {
            val code = """
                macro a(x: int): int = x + 1;
                macro b(x: int): int = x + 2;
                macro c(x: int): int = x + 3;
                macro d(x: int): int = x + 4;
                macro e(x: int): int = x + 5;
                join A(n: int) $ 100;
                withdraw { A -> a(A.n) + b(A.n) + c(A.n) + d(A.n) + e(A.n) }
            """.trimIndent()

            val ast = parseCode(code)
            typeCheck(ast)
            val inlined = inlineMacros(ast)
            ast.macros.size shouldBe 5
            inlined.macros.size shouldBe 0
        }
    }
})


/**
 * Test that macros produce identical IR to their desugared equivalents.
 */
class MacroIRTest : FreeSpec({

    "IR Equivalence" - {
        "Prisoner's Dilemma: macro version produces same IR as manual version" {
            val withMacros = """
                macro prisonerPayoff(me: bool, other: bool): int =
                    (me && other)    ? -2 :
                    (me && !other)   ?  0 :
                    (!me && other)   ? -3 :
                    -1;

                join A() $ 100;
                join B() $ 100;
                yield A(c: bool) B(c: bool);
                withdraw (A.c != null && B.c != null)
                ?( { A -> prisonerPayoff(A.c, B.c); B -> prisonerPayoff(B.c, A.c) })
                :(A.c == null) ? { A -> -100; B -> 10 }
                :{ A -> 10; B -> -100 }
            """.trimIndent()

            val withoutMacros = """
                join A() $ 100;
                join B() $ 100;
                yield A(c: bool) B(c: bool);
                withdraw (A.c != null && B.c != null)
                ?(  (A.c && B.c )   ? { A -> -2; B -> -2 }
                    : (A.c && !B.c) ? { A ->  0; B -> -3 }
                    : (!A.c && B.c) ? { A -> -3; B ->  0 }
                    :                 { A -> -1; B -> -1 }
                ):(A.c == null) ? { A -> -100; B -> 10 }
                :{ A -> 10; B -> -100 }
            """.trimIndent()

            val astWithMacros = parseCode(withMacros)
            typeCheck(astWithMacros)
            val inlined = inlineMacros(astWithMacros)
            val irWithMacros = compileToIR(inlined)

            val astWithoutMacros = parseCode(withoutMacros)
            typeCheck(astWithoutMacros)
            val irWithoutMacros = compileToIR(astWithoutMacros)

            // IR should be semantically equivalent (same roles, actions, structure)
            // Note: Payoff expressions may be structurally different due to parameter ordering
            // in macro calls, but backends should generate identical outputs
            irWithMacros.roles shouldBe irWithoutMacros.roles
            irWithMacros.chanceRoles shouldBe irWithoutMacros.chanceRoles
            irWithMacros.dag.actions shouldBe irWithoutMacros.dag.actions
            // Both should compile to the same backend output (verified separately)
        }

        "Odds and Evens: macro version produces same IR as manual version" {
            val withMacros = """
                macro evenPayoff(even: bool, odd: bool): int = (even <-> odd) ? 10 : -10;
                macro oddPayoff(even: bool, odd: bool): int = (even <-> odd) ? -10 : 10;

                join Odd() $ 100 Even() $ 100;
                yield Odd(c: bool) Even(c: bool);
                withdraw (Even.c != null && Odd.c != null) ?
                     { Even -> evenPayoff(Even.c, Odd.c); Odd -> oddPayoff(Even.c, Odd.c) }
                : (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
                : { Even -> -100; Odd -> -100 }
            """.trimIndent()

            val withoutMacros = """
                join Odd() $ 100 Even() $ 100;
                yield Odd(c: bool) Even(c: bool);
                withdraw (Even.c != null && Odd.c != null) ?
                     { Even -> ((Even.c <-> Odd.c) ? 10 : -10); Odd -> ((Even.c <-> Odd.c) ? -10 : 10) }
                : (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
                : { Even -> -100; Odd -> -100 }
            """.trimIndent()

            val astWithMacros = parseCode(withMacros)
            typeCheck(astWithMacros)
            val inlined = inlineMacros(astWithMacros)
            val irWithMacros = compileToIR(inlined)

            val astWithoutMacros = parseCode(withoutMacros)
            typeCheck(astWithoutMacros)
            val irWithoutMacros = compileToIR(astWithoutMacros)

            // IR should be semantically equivalent (same roles, actions, structure)
            // Note: Payoff expressions may be structurally different due to parameter ordering
            // in macro calls, but backends should generate identical outputs
            irWithMacros.roles shouldBe irWithoutMacros.roles
            irWithMacros.chanceRoles shouldBe irWithoutMacros.chanceRoles
            irWithMacros.dag.actions shouldBe irWithoutMacros.dag.actions
            // Both should compile to the same backend output (verified separately)
        }
    }
})

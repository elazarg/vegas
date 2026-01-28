# Testing Gaps Analysis

**Status:** Draft
**Scope:** Systematic inventory of missing tests across all layers of the Vegas compiler and runtime, with design sketches for addressing each gap.

**Related Documents:**
- `DESIGN.md` - DAG & proof-game design (defines the semantic model under test)
- `LIVENESS.md` - Fair-play liveness specification (identifies where-clause satisfiability as a semantic concern)
- `SUBGAMES.md` - Quit semantics and handler design (defines bail-out behavior)

---

## 0. Framing: What the Current Tests Actually Prove

The existing test suite is strong on **positive functional correctness**: valid programs compile, valid traces execute, and outputs match golden masters. But the suite has a systematic blind spot: it almost never asks "does the system *reject* what it should reject?"

### 0.1 The Trace-Inclusion Problem

The Ethereum model tests (`EthModelTest`) verify:

> For each trace `t` in the semantic model, playing `t` on the deployed Solidity contract produces the same payoffs.

Formally, letting `L(S)` be the traces of the semantic model and `L(C)` the traces accepted by the contract:

```
L_tested ⊆ L(S)  ∧  ∀t ∈ L_tested: payoff_S(t) = payoff_C(t)
```

where `L_tested` is either exhaustive enumeration (small games) or random sampling (large games) of `L(S)`.

This establishes **one-directional inclusion** of tested model traces into contract traces. It does *not* test:

1. **Exhaustiveness of sampling** — `L_tested` may miss corner-case traces in `L(S)`.
2. **Contract rejects illegal traces** — No test submits a trace `t ∉ L(S)` and checks that the contract reverts.
3. **Semantic model rejects illegal moves** — The `TraceEnumerator` filters by guards *before* building traces (line 229 of `Semantics.kt`), so guard-violating values are never generated, let alone tested for rejection.

### 0.2 Levels of Testing

We identify six levels, from surface syntax down to deployed contracts:

| Level | What it tests | Current coverage | Key gap |
|-------|--------------|------------------|---------|
| 1. Parser | Syntax recognition | Indirect only | No error/recovery tests |
| 2. Type checker | Static type constraints | Strong positive + negative | Missing conservation, handler types |
| 3. Semantic model | Game dynamics | Positive traces only | No guard rejection, no information hiding |
| 4. Backend codegen | Output correctness | Golden masters (5 games) | No negative programs, few games |
| 5. EVM integration | On-chain correctness | Positive traces + timeout | No illegal moves, no security |
| 6. Cross-layer | Consistency across layers | None | Entirely missing |

---

## 1. Parser Level

### 1.1 Current State

No dedicated parser test file exists. Parsing is tested only indirectly:
- `ExamplesValidationTest` verifies all `.vg` example files parse successfully.
- `MacroTest` exercises macro-related parsing.
- `ActionDagTypecheckTest` parses valid/invalid files.

### 1.2 Missing Tests

**Error recovery and diagnostics:**
- Unclosed braces/brackets/parentheses
- Missing semicolons after statements
- Invalid token sequences (e.g., `yield yield`)
- Misspelled keywords (`jion` for `join`)
- Empty game body, empty role list
- Unterminated string literals (if any)

**Edge cases:**
- Empty file
- File with only comments
- Deeply nested expressions (stack depth)
- Very long identifiers or numeric literals

**Error message quality:**
- Line and column numbers in parse errors
- Helpful suggestions (e.g., "did you mean `join`?")

### 1.3 Design Sketch

```
class ParserErrorTest : FunSpec({
    // Each test provides malformed .vg source and asserts:
    // (a) parsing throws a structured error (not an NPE or ClassCast)
    // (b) the error message contains a line number
    // (c) partial parse results are reasonable (if error recovery is added)

    test("unclosed brace") {
        shouldThrow<ParseException> {
            parseString("game Foo { join A(deposit $1); ")
        }.message shouldContain "line"
    }
})
```

Priority: **Low**. ANTLR provides reasonable default error handling. Parser-level gaps rarely cause silent correctness bugs.

---

## 2. Type Checker Level

### 2.1 Current State

`TypeCheckerTest.kt` (~1,050 lines) has strong coverage of positive and negative cases: type mismatches, undefined roles/members, hidden field access, commit-without-reveal, set types, where clauses, let bindings, macros.

### 2.2 Missing Tests

**Conservation property:**
The Vegas language guarantees that every terminal `withdraw` allocates the entire pool exactly. No type-checker test verifies this is enforced or that violations produce clear errors.

```
// Should reject: payouts don't sum to pool
withdraw { A -> $1; B -> $1 }  // pool is $3
```

**Handler expression typing:**
`|| handler` blocks in quit continuations should be type-checked for the same constraints as top-level outcomes. No tests verify handler expression types or the availability rule (handler code cannot reference the failed action's values).

**Duplicate role declarations:**
What happens if the same role appears twice in a role list? Or the same parameter name in an action?

**Deposit constraints:**
Negative deposits, zero deposits, deposit type mismatches. The compiler presumably rejects these, but no test verifies it.

**Scope boundaries:**
- Let-bound variable used outside its scope
- Macro parameter name shadowing a role name
- Action parameter shadowing a macro parameter

### 2.3 Design Sketch

```
test("conservation: underpayment rejected") {
    shouldThrow<StaticError> {
        typeCheck(parseString("""
            game Bad {
                join A(deposit $5); join B(deposit $5);
                withdraw { A -> $3; B -> $3 }  // $6 != $10
            }
        """))
    }.message shouldContain "conservation"
}
```

Priority: **Medium**. Conservation and handler typing are semantic invariants that, if violated, produce incorrect contracts.

---

## 3. Semantic Model Level

### 3.1 Current State

Four test files cover the semantic model:
- `SemanticsTest` — move enumeration, terminal detection, quit availability
- `ConfigurationTest` — state structure, hiding, redaction
- `TransitionTest` — move application, frontier finalization, history
- `LabelTest` — label structure

All tests use valid moves and check that the model correctly advances state.

### 3.2 Missing Tests

#### 3.2.1 Guard Clause Rejection (Critical)

The semantic model's `enumerateAssignmentsForAction()` (Semantics.kt:229) filters assignments by evaluating guard expressions. But no test ever constructs a move that *violates* a guard and verifies the model rejects it.

The `TraceEnumerator` only generates guard-satisfying assignments, so the Ethereum model tests never exercise this path either. This is the gap the current discussion identified.

**What to test:**
- Submit a `GameMove` with assignments that violate the `where` clause
- Verify the semantic model either (a) does not list it as a legal move, or (b) rejects it on submission
- Test with each guard type: equality, inequality, `alldiff`, boolean combinations

**Example (MontyHall):**
```
yield Host(goat: door) where Host.goat != Guest.d
```
After Guest chooses door 1, submitting `Host.goat = 1` should be rejected.

#### 3.2.2 Information Hiding Correctness

The `Configuration` tracks which values each role can see (via `playerView` / `heapForRole`). No test verifies that:
- A role's view does not contain another role's committed (not yet revealed) values
- After reveal, the value becomes visible to all roles
- Guard evaluation uses the correct knowledge scope (actor sees own hidden choice)

#### 3.2.3 Commit-Reveal Consistency

No test verifies that the revealed value must match the committed value. In `LocalRuntime`, this may be trivially guaranteed by implementation (auto-reveal from history). But the semantic model should explicitly enforce it, and tests should verify the enforcement.

#### 3.2.4 Payoff Evaluation

No test evaluates payoff expressions against a known game outcome and checks the numeric result. The model tests compare LocalRuntime vs EthereumRuntime payoffs, but both could be wrong in the same way.

**What to test:**
- Hand-compute expected payoffs for specific traces of known games
- Compare against `session.payoffs()` on LocalRuntime
- Cover: normal play, quit paths, all-quit, mixed quit

#### 3.2.5 Frontier Ordering Independence

When multiple roles act in the same frontier, the final state should be independent of submission order. No test exercises this: e.g., submit A then B vs B then A, check same result.

#### 3.2.6 Quit Propagation

Limited testing of quit persistence across frontiers. Verify:
- A quitted role cannot act in subsequent frontiers
- Downstream actions that depend on a quitted action see the quit
- Handler expressions evaluate correctly with quit context

### 3.3 Design Sketch

```kotlin
class GuardRejectionTest : FunSpec({
    test("MontyHall: Host cannot reveal same door as Guest") {
        val game = loadGame("MontyHall")
        val semantics = GameSemantics(game)
        var config = Configuration.initial(game)
        // ... advance to Host's move after Guest picks door 1 ...

        val illegalMove = GameMove(
            actionId = hostActionId,
            role = host,
            visibility = Visibility.PUBLIC,
            assignments = mapOf(goatVar to Expr.Const.IntVal(1)) // same as Guest
        )

        // The illegal move should not appear in legal moves
        val legalMoves = semantics.enabledLabels(config)
            .filterIsInstance<Label.Play>()
        legalMoves.flatMap { it.assignments.values }
            .shouldNotContain(mapOf(goatVar to Expr.Const.IntVal(1)))
    }
})
```

Priority: **High**. Guard rejection is the core semantic guarantee of Vegas. Without these tests, we cannot be confident that where-clause constraints are enforced.

---

## 4. Backend Code Generation Level

### 4.1 Current State

Ten backend golden-master test files, each testing the same five games: MontyHall, OddsEvensShort, Prisoners, TicTacToe, VickreyAuction. Tests compare generated output byte-for-byte against stored golden masters.

A Solidity determinism test verifies repeated compilation produces identical output.

### 4.2 Missing Tests

**Negative input programs:**
No test feeds an invalid or degenerate IR to a backend and checks for graceful failure. For example:
- Game with zero roles
- Game with no actions
- Game with cyclic dependencies (should be caught by DAG construction, but what if it isn't?)

**Broader game coverage:**
Only 5 of ~20 example games have golden masters. Games with distinctive features are untested at the golden-master level:
- `Centipede` — sequential chain with `|| null` handlers
- `Simple` — minimal commit-reveal
- `RPSLS` — five-element set type
- `EscrowContract` — three roles with arbiter

**Backend-specific property validation:**
- **Solidity**: Generated contract compiles with `solc` (currently only tested in Ethereum integration tests, not in golden-master tests)
- **Gambit EFG**: Strategy set has correct cardinality; information sets are consistent
- **SMT-LIB**: Generated constraints are satisfiable for valid traces (check with z3)

**Cross-backend semantic consistency:**
No test verifies that different backends encode the same game semantics. For example, the Gambit EFG and the Solidity contract should agree on the set of valid traces and their payoffs. This is partially addressed by `GambitSemanticTest` (which unrolls and checks structure), but not by comparing across backends.

### 4.3 Design Sketch

Expand golden masters to cover all example games. Add a `SolidityCompilationTest` that runs `solc` on every generated `.sol` file (where `solc` is available).

Priority: **Medium**. Golden-master tests catch regressions in output format but don't validate semantic correctness of the output.

---

## 5. EVM Integration Level

### 5.1 Current State

- **EthSmokeTest**: Hand-written scenarios for Prisoners and OddsEvensShort.
- **EthModelTest**: Exhaustive/sampled trace comparison across 14 games.
- **EthTimeoutModelTest**: Parametric timeout testing for 3 games (6 test cases).

All tests submit *legal* moves and verify *correct* payoffs.

### 5.2 Missing Tests

#### 5.2.1 Guard Rejection on Contract (Critical)

The Solidity backend translates `where` guards into `require` statements. No test submits a guard-violating transaction and verifies the contract reverts.

This is the EVM-side counterpart of the semantic-level guard rejection gap (Section 3.2.1). It is independent and should be tested separately: the semantic model might correctly enumerate legal moves while the generated Solidity fails to enforce the same guard.

**What to test for each guard type:**
- Equality guard violation (`where Host.goat != Guest.d` → submit matching value)
- Domain guard violation (value outside the declared set type)
- Boolean guard violation (submit `false` when guard requires `true`)
- Compound guard violation (conjunctive/disjunctive conditions)

#### 5.2.2 Role Enforcement

The Solidity `by(Role)` modifier restricts which Ethereum address can call each function. No test verifies:
- Wrong address submitting a move → revert
- Correct address submitting → success (implicitly tested, but not explicitly as a security property)

#### 5.2.3 Action Ordering Enforcement

The Solidity `depends` modifier enforces action dependencies. No test verifies:
- Submitting an action before its dependency → revert
- Submitting an action after its dependency → success
- Re-submitting an already-completed action → revert

#### 5.2.4 Deposit Validation

The `join` modifier enforces `msg.value == deposit`. No test verifies:
- Joining with too little ETH → revert
- Joining with too much ETH → revert (or refund, depending on implementation)
- Joining with exactly correct amount → success

#### 5.2.5 Commitment Integrity

For commit-reveal games, the Solidity contract stores `keccak256(abi.encodePacked(value, salt))` at commit time and verifies the hash matches at reveal time. No test verifies:
- Revealing a different value than committed → revert
- Revealing with wrong salt → revert
- Revealing correct value + salt → success

This is a critical security property: if commitment integrity is broken, a player can observe the opponent's commit, then reveal a strategically chosen value.

#### 5.2.6 Replay Protection

No test verifies that:
- Submitting the same move twice → second submission reverts
- The contract's state machine advances correctly and doesn't allow replays

#### 5.2.7 Withdrawal Correctness

No test verifies that `executeWithdrawals()` sends the exact correct amounts. The model tests compare payoffs, but the actual ETH balance changes are not checked against expected values. A bug in the withdrawal logic could send wrong amounts while the payoff *reporting* looks correct.

#### 5.2.8 Bidirectional Trace Inclusion

The current tests verify:

```
∀t ∈ L_tested(S): contract accepts t ∧ payoff_C(t) = payoff_S(t)
```

The missing direction is:

```
∀t ∉ L(S): contract rejects t
```

This requires generating *illegal* traces — moves that the semantic model would not enumerate — and verifying the contract reverts. Categories of illegal traces:
- Domain violations (out-of-range parameter values)
- Guard violations (where clause failures)
- Ordering violations (wrong action sequence)
- Role violations (wrong actor)
- Commitment violations (mismatched reveal)

### 5.3 Design Sketch

```kotlin
class EthNegativeTest : FunSpec({
    val anvil = AnvilNode()
    beforeSpec { anvil.start() }
    afterSpec { anvil.stop() }

    test("MontyHall: Host guard violation reverts") {
        val game = loadGame("MontyHall")
        val rpc = EthJsonRpc(anvil.rpcUrl)
        val runtime = EthereumRuntime(rpc, anvil.accounts)
        val session = runtime.deploy(game) as EthereumSession

        // Play joins + Guest commits door 1
        // ...

        // Host tries to reveal goat = same door as Guest → should revert
        val illegalMove = GameMove(
            actionId = hostRevealId,
            role = hostRole,
            visibility = Visibility.PUBLIC,
            assignments = mapOf(goatVar to Expr.Const.IntVal(1))
        )

        shouldThrow<TxRevertedException> {
            session.submitMove(illegalMove)
        }
    }

    test("Prisoners: wrong role reverts") {
        // A's address tries to submit B's move
    }

    test("Prisoners: wrong deposit reverts") {
        // Join with deposit - 1 wei
    }

    test("Prisoners: commitment forgery reverts") {
        // Commit value X, reveal value Y
    }
})
```

Priority: **High**. These are security-critical properties of deployed smart contracts. The absence of negative EVM tests means we have no automated verification that the generated contracts enforce game rules.

---

## 6. Cross-Layer Consistency

### 6.1 Current State

No tests verify consistency across layers. Each layer is tested in isolation (or against one adjacent layer, as in EthModelTest which compares semantic model vs EVM).

### 6.2 Missing Tests

**Semantic model vs type checker:**
If the type checker accepts a program, the semantic model should be able to execute it without internal errors. No test verifies this for all example games.

**Semantic model vs Gambit EFG:**
The EFG backend encodes game trees. The set of terminal histories in the EFG should correspond to the traces enumerable from the semantic model. No test compares these.

**Semantic model vs SMT encoding:**
The SMT encoding should be satisfiable for exactly the traces the semantic model allows. No test checks this (would require running z3).

**Type checker vs backends:**
If the type checker rejects a program, no backend should silently produce output. No test verifies this.

### 6.3 Design Sketch

```kotlin
class CrossLayerConsistencyTest : FunSpec({
    test("all examples: parse + typecheck + compile + semantic model runs without error") {
        for (name in allExampleNames) {
            val game = loadAndCompile(name)
            val traces = TraceEnumerator.exhaustive(game, maxTraces = 5)
            traces.shouldNotBeEmpty()
        }
    }

    test("all examples: EFG terminal count matches trace count") {
        // For small games where exhaustive enumeration is feasible
    }
})
```

Priority: **Medium**. Cross-layer inconsistencies are subtle bugs that might only manifest when combining features. A basic smoke test across all examples would catch regressions.

---

## 7. Summary and Prioritization

### Tier 1 — Semantic Correctness (High Priority)

| Gap | Level | Risk |
|-----|-------|------|
| Guard clause rejection | Semantic model | Silent acceptance of illegal moves |
| Guard enforcement on contract | EVM integration | Contract fails to enforce game rules |
| Commitment integrity | EVM integration | Players can cheat at commit-reveal |
| Payoff evaluation against hand-computed values | Semantic model | Both LocalRuntime and EVM could be wrong |

These gaps undermine the core value proposition of Vegas: that a single specification generates correct implementations. If guards aren't enforced, the generated contract doesn't implement the specified game.

### Tier 2 — Security Properties (High Priority for EVM)

| Gap | Level | Risk |
|-----|-------|------|
| Role enforcement (wrong address) | EVM integration | Unauthorized move submission |
| Deposit validation | EVM integration | Financial loss or contract stuck |
| Replay protection | EVM integration | State corruption |
| Action ordering | EVM integration | Bypassing game flow |
| Withdrawal correctness (ETH balances) | EVM integration | Incorrect fund distribution |

These are standard smart contract security concerns. While the generated Solidity uses well-known patterns (`by`, `depends`, `require`), the *correctness of the code generation* that produces these patterns is untested.

### Tier 3 — Robustness and Coverage (Medium Priority)

| Gap | Level | Risk |
|-----|-------|------|
| Conservation property | Type checker | Payoffs don't sum correctly |
| Handler expression typing | Type checker | Runtime errors in quit paths |
| Information hiding correctness | Semantic model | Players see hidden values |
| Broader golden-master games | Backend codegen | Regressions in untested backends |
| Cross-backend consistency | Cross-layer | Backends disagree on semantics |
| Bidirectional trace inclusion | EVM integration | Incomplete security guarantee |

### Tier 4 — Completeness (Lower Priority)

| Gap | Level | Risk |
|-----|-------|------|
| Parser error recovery | Parser | Poor developer experience |
| Frontier ordering independence | Semantic model | Non-deterministic behavior |
| Quit propagation edge cases | Semantic model | Incorrect handler activation |
| Backend negative input | Backend codegen | Unhelpful error messages |
| Solidity compilation check | Backend codegen | Generated code doesn't compile |

---

## 8. Testing Strategy: Guard Rejection

Since guard rejection was identified as the most critical cross-cutting gap, this section sketches a systematic approach.

### 8.1 Guard Taxonomy

Vegas `where` clauses generate guards at two levels:

1. **Domain guards** (implicit): Parameter value must be within the declared type's domain. For `x: {0,1,2}`, submitting `x = 5` is a domain violation.

2. **Explicit guards**: The `where` keyword introduces an arbitrary boolean expression over the action's parameters and visible history. For `where Host.goat != Guest.d`, submitting a matching value is a guard violation.

### 8.2 Test Generation Approach

For each game with guards:

1. **Enumerate guard-satisfying assignments** (already done by `enumerateAssignmentsForAction`).
2. **Generate guard-violating assignments** by:
   - For domain guards: pick values outside the type's range
   - For explicit guards: negate the guard, solve for a satisfying assignment of the negation
   - Simpler: for small domains, the complement of legal assignments *is* the set of illegal assignments

3. **Submit each illegal assignment** to both:
   - The semantic model (verify it's not in `legalMoves()`)
   - The deployed contract (verify the transaction reverts)

### 8.3 Scope

Start with games that have explicit `where` clauses:
- `MontyHall` — `where Host.goat != Guest.d`
- `VickreyAuction` — `where Seller.winner == ...` (conditional assignment)
- `Centipede` — no explicit guards, but sequential dependency
- `Prisoners` — no guards (all values legal), but commit-reveal

For domain-only guards, all games with set-typed parameters are candidates.

---

## 9. Implemented Tests (2026-01-28)

Based on this analysis, the following tests were implemented using equivalence class partitioning to maximize coverage while minimizing redundancy.

### 9.1 Tests Added

#### GuardRejectionTest.kt (Semantic Model Level)

Addresses §3.2.1 — verifies guard enforcement through move enumeration.

| Test | Equivalence Class | What It Verifies |
|------|------------------|------------------|
| MontyHall: door type restricts to {0,1,2} | Domain guards | Parameter values are within declared type |
| TicTacToe: cell values restricted to domain | Domain guards | Integer ranges enforced |
| MontyHall: goat options exclude Guest's door | Inequality guards | `where Host.goat != Guest.d` |
| TicTacToe: second player cannot reuse cell | Alldiff guards | `alldiff` constraint enforced |

**Design decision**: Rather than trying to submit illegal moves (which would require bypassing `legalMoves()`), tests verify that the enumeration itself correctly excludes guard-violating values. This tests the semantic guarantee from the user's perspective.

#### PayoffEvaluationTest.kt (Semantic Model Level)

Addresses §3.2.4 — verifies payoff computation against hand-computed expectations.

| Test | Equivalence Class | What It Verifies |
|------|------------------|------------------|
| Prisoners: payoffs sum to 200 | Conservation property | Total deposits = total payoffs |
| Dominance: payoffs sum to 20 | Conservation property | Different deposit amounts |
| Simple: payoffs sum to 12 | Conservation property | Smaller pool |
| Trivial1: payoffs sum to 10 | Conservation property | Minimal game |
| All roles have non-negative payoffs | Non-negativity | Payoffs ≥ 0 |
| Games reach terminal state | Terminal detection | Default play reaches completion |
| Prisoners: both cooperate → 100/100 | Specific outcome | Hand-computed expected result |

**Design decision**: Tests use `playToTerminal()` with first-move selection to ensure deterministic behavior. Conservation is tested across multiple games with different pool sizes.

#### EthNegativeTest.kt (EVM Integration Level)

Addresses §5.2 — verifies EVM contracts reject illegal operations.

| Test | Section | What It Verifies |
|------|---------|------------------|
| Prisoners: wrong role address reverts | §5.2.2 | `by(Role)` modifier enforcement |
| Prisoners: action before dependency reverts | §5.2.3 | `depends` modifier enforcement |
| Prisoners: wrong deposit amount reverts | §5.2.4 | `msg.value` validation |
| OddsEvensShort: commitment forgery reverts | §5.2.5 | Hash verification on reveal |
| Prisoners: replay action reverts | §5.2.6 | State machine prevents replay |

**Design decision**: Tests bypass the session's move enumeration by constructing raw transactions with `AbiCodec` and submitting directly to the contract. This allows testing rejection of moves that would never be generated by `legalMoves()`.

### 9.2 Bug Discovered: OddsEvensShort Move Enumeration

During test development, a bug was discovered in the semantic model's move enumeration for OddsEvensShort.

**Symptom**: PayoffEvaluationTest initially failed for OddsEvensShort because the game never reached terminal state.

**Investigation**: Debug comparison between Prisoners (which works) and OddsEvensShort revealed:

```
=== Prisoners (working) ===
Step 3: 6 moves
  A: {c=Hidden(inner=BoolVal(v=true))}
  A: {c=Hidden(inner=BoolVal(v=false))}
  B: {c=Hidden(inner=BoolVal(v=true))}
  ...
→ Correctly enumerates boolean values for 'c' parameter
→ Reaches terminal state

=== OddsEvensShort (broken) ===
Step 1: 2 moves
  Odd: {}
  Even: {}
Step 2: 2 moves
  Odd: {}
  Even: {}
... (repeats indefinitely with empty assignments)
→ Never enumerates parameter values
→ Never reaches terminal state
```

**Root cause**: The semantic model's `enumerateAssignmentsForAction()` returns moves with **empty `assignments` maps** for OddsEvensShort's yield actions, instead of properly enumerating the `c: bool` parameter values. This prevents the game from ever progressing past the yield phase.

**Impact**:
- OddsEvensShort cannot be played to completion using `LocalRuntime`
- The EthModelTest for OddsEvensShort likely succeeds because it uses exhaustive trace enumeration from a different path
- The EthSmokeTest works because it manually constructs moves rather than relying on `legalMoves()`

**Workaround applied**: PayoffEvaluationTest excludes OddsEvensShort from conservation tests. The EthNegativeTest for commitment integrity uses OddsEvensShort but manually constructs moves.

**Status**: Bug identified but not fixed. Requires investigation of `TraceEnumerator` or `GameSemantics.enumerateAssignmentsForAction()` to determine why parameter enumeration fails for this game structure.

### 9.3 Tests Not Added (With Rationale)

The following gaps from §1-8 were not addressed in this round:

| Gap | Reason |
|-----|--------|
| Parser error tests (§1) | Low priority; ANTLR provides default handling |
| Conservation type check (§2.2) | Requires compiler modification, not just test addition |
| Information hiding (§3.2.2) | Complex to verify; would require introspection of role views |
| Guard rejection at EVM level (§5.2.1) | Requires bypassing session entirely; partial coverage via commitment test |
| Cross-layer consistency (§6) | Would require z3/external tools; deferred |

### 9.4 Redundancy Analysis

No existing tests were removed. The new tests were designed to complement rather than duplicate existing coverage:

- `EthModelTest` verifies positive traces match between semantic model and EVM
- New tests verify *rejection* of illegal operations (the missing direction)
- `GuardRejectionTest` tests enumeration, not move submission
- `PayoffEvaluationTest` tests against hand-computed values, not just cross-runtime comparison

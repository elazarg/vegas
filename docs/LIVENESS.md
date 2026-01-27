# Fair-Play Liveness Specification

## Overview

This document specifies semantic requirements for guaranteeing **fair-play liveness** in Vegas - ensuring that players who intend to play fairly are never forced into abandonment by computational impossibility.

---

## 1. The Problem

Vegas currently handles *strategic* abandonment via quit handlers (`|| split`, `|| burn`, `|| null`). However, there's a gap: `where` clauses can force a player to quit even when they want to continue playing.

### 1.1 Abandonment vs Inability

Currently, Vegas treats `Quit` as a strategic move (SUBGAMES.md §3.1). But there's a critical distinction:

- **Strategic abandonment**: Player *chooses* not to continue (unfavorable position, external factors)
- **Computational inability**: Player *cannot* continue because no valid move exists or finding one is intractable

From a game-theoretic perspective, these are fundamentally different:
- Strategic quit → player bears responsibility; handlers may penalize
- Computational inability → NOT the player's fault; penalization is unfair

### 1.2 Two Sources of Inability

**Source 1: Unsatisfiable constraints**

A `where` clause that either:
- IS unsatisfiable statically: `where x > 10 && x < 5`
- MAY BECOME unsatisfiable dynamically: depends on prior moves that create impossible situations

Example of dynamic unsatisfiability:
```
yield Alice(x: int);
yield Bob(y: int) where y != Alice.x && y != Alice.x + 1 && y != Alice.x - 1;
```
If `int` is `{0, 1, 2}` and Alice plays `x = 1`, Bob has no valid move.

**Source 2: Computationally intractable constraints**

A `where` clause that is satisfiable but finding a witness is computationally infeasible:
```
yield Alice(p: int, q: int) where p * q == N;  // N is a large semiprime
```
Satisfiable (by definition of semiprime), but finding p, q requires factoring.

---

## 2. Core Principle

**Fair-play liveness**: A player acting in good faith must always be able to produce *some* valid move, and doing so must be computationally tractable.

This implies:

1. If a value is guarded by a `where` clause that might block fair play, the type system must reflect this uncertainty
2. The value should be typed as `opt T` (optional) unless we can prove fair-play liveness
3. Downstream code must handle the possibility that no value was produced (not due to quit, but due to impossibility)

---

## 3. Proposed Semantic Rule

A value `v: T` guarded by `where φ(v)` should be typed as:
- `T` (non-optional) if **both** conditions hold:
  1. **Universal Satisfiability**: We can prove `∃v. φ(v)` is satisfiable for **ALL** reachable game states (not just some)
  2. **Tractability**: A witness expression can be provided that is verified to always satisfy `φ`

- `opt T` (optional) otherwise

The universal satisfiability requirement is intentionally conservative: if ANY opponent strategy can lead to a state where the constraint is unsatisfiable, the value must be optional.

**Implementation phasing**: Satisfiability validation is the near-term priority. Tractability validation is deferred to a future phase.

### 3.1 Satisfiability Validation (Near-term)

Satisfiability answers: "Does at least one valid value exist for every reachable game state?"

**For enumerable domains** (finite types like `{0,1,2}` or `bool`):
- Exhaustive enumeration proves satisfiability
- For every possible assignment of prior fields, check if at least one value in the domain satisfies `φ`
- This can leverage existing EFG generation infrastructure: the Gambit backend already enumerates game states and checks guard satisfaction (`enumerateAssignmentsForAction` in `Semantics.kt`)
- Implementation is straightforward - mostly plumbing to surface the satisfiability check as a type-level requirement

**For infinite domains**:
- Static analysis of the constraint form (e.g., linear arithmetic has decidable satisfiability)
- Requires constraint solver integration (SMT)
- Deferred: infinite domains without satisfiability proof default to `opt T`

**Escape hatch - null acceptance**:
- If `|| null` handler is present AND `null` trivially satisfies the fairness requirement (player is not penalized for producing no value), then `opt T` is acceptable and fair-play is preserved

### 3.2 Tractability Validation (Future)

Tractability answers: "Can we efficiently *find* a valid value, not just prove one exists?"

Even if satisfiability is proven, finding a witness at runtime may be intractable. The proposed solution:

**Witness expressions**: A witness is a Vegas expression `w` such that:
1. `w` is well-typed with type `T`
2. The compiler can verify that `φ(w)` holds for all reachable game states
3. The expression `w` itself is computable (no unbounded search)

Example:
```
// Constraint
yield Host(goat: door) where goat != Guest.d && goat != Host.car;

// Witness expression (one possible approach)
witness: (Guest.d == 0 && Host.car == 0) ? 1
       : (Guest.d == 0 || Host.car == 0) ? 2
       : 0
```

The witness expression proves that a value can be *constructed*, not just that one exists.

**For enumerable domains**:
- Enumeration is O(|domain|) - tractable for small finite sets
- A trivial witness strategy: enumerate and return first satisfying value
- Both satisfiability AND tractability come "for free" from the existing enumeration infrastructure

**For infinite domains**:
- Requires explicit witness expressions or proof that the constraint belongs to a tractable class
- Examples of tractable: linear integer arithmetic (witnesses constructible)
- Examples of intractable: factoring, discrete log, general SAT
- Without witness: default to `opt T`

---

## 4. Implications

### 4.1 Type System Changes

The type of a yielded/revealed value depends on its `where` clause:

| Condition | Current Type | Proposed Type |
|-----------|--------------|---------------|
| No `where` clause | `T` (or `opt T` without handler) | unchanged |
| Provably satisfiable + tractable | `T` | `T` |
| Possibly unsatisfiable | `T` (or `opt T` without handler) | **must be `opt T`** |
| Satisfiable but intractable | `T` (or `opt T` without handler) | **must be `opt T`** |

### 4.2 Downstream Code

Code that consumes values from constrained actions must handle optionality:
- `isDefined(Bob.y)` / `isUndefined(Bob.y)` checks
- Payoff expressions must account for the "couldn't play" case
- This is structurally similar to quit handling but semantically distinct

### 4.3 Game-Theoretic Interpretation

**Design decision: Inability is fully distinct from Quit.**

In extensive-form game terms:
- A constrained action with `opt T` has an implicit "pass" move when the constraint is unsatisfiable
- This "pass" is **NOT** equivalent to "quit":
  - It MUST NOT trigger quit handlers (`|| split`, `|| burn`, custom handlers)
  - It MUST NOT forfeit stakes or penalize the player
  - The player's deposit remains protected
- Semantically, it's "Nature blocks this branch" - the player had no choice and bears no responsibility
- This is fundamentally different from strategic quit where handlers and forfeiture apply

The type system must distinguish these cases so backends can generate appropriate code:
- `opt T` from inability → no penalty, game continues with null value
- `opt T` from quit → handlers apply, potential forfeiture

### 4.4 Type-Level Distinction

The type system must distinguish between two sources of optionality:

| Source | Type Annotation | Handler Triggered? | Forfeit? |
|--------|-----------------|-------------------|----------|
| Strategic quit | `opt T` from quit handler | Yes | Yes (per handler) |
| Computational inability | `opt T` from unproven liveness | **No** | **No** |

This suggests the IR may need to track the *reason* for optionality, not just the type itself. Possible approaches:
- Two distinct optional type constructors (e.g., `QuitOpt T` vs `ConstraintOpt T`)
- Metadata on fields indicating the source of optionality
- Separate "pass" action in the DAG distinct from "quit" action

The exact representation is an implementation choice, but the semantic distinction is mandatory.

### 4.5 Backend Implications

**Gambit backend**: Already handles this correctly for enumerable types - if no value satisfies the guard, the frontier is empty. The semantic model should distinguish "empty frontier due to constraint" from "player chose to quit."

**Solidity backend**: Must generate code that allows the action to complete with a null/none value when the constraint is unsatisfiable. This is different from timeout-triggered quit. The contract must:
- Allow the constrained role to submit a "no valid move" transaction
- NOT penalize or trigger forfeiture
- Continue the game with null value

**Gallina backend**: The FAIR_PLAY policy (which assumes no quits) must account for computational inability as a distinct case. A game can be "fair-play complete" even if some constraints are occasionally unsatisfiable, as long as this is tracked and handled without penalty.

---

## 5. Relationship to Existing Constructs

### 5.1 Relationship to `|| null` Handler

The `|| null` handler currently means "if player quits, treat value as optional."

Under this proposal, values with unproven fair-play liveness become `opt T` regardless of handler presence. The `|| null` handler would serve a different purpose: specifying what happens on strategic quit, not computational inability.

Alternatively, `|| null` could be extended to mean "I acknowledge this constraint may be impossible" - making it an explicit opt-in to potential inability.

### 5.2 Relationship to Enumerable Types

Vegas already implicitly distinguishes enumerable types (from CLAUDE.md and Gambit backend):
- `BoolType`: enumerable, 2 values
- `SetType`: enumerable, explicit finite domain
- `IntType`: NOT enumerable, throws error in Gambit

This distinction is key: enumerable types have automatic tractability proofs. The proposal leverages this existing categorization.

### 5.3 Relationship to Commit-Reveal

Commit-reveal doesn't change the analysis - the `where` clause on `reveal` is still subject to the same satisfiability/tractability requirements. A committed value that cannot be validly revealed is still a fair-play violation.

---

## 6. Open Questions

### 6.1 What constitutes "tractable"? (Deferred)

Tractability validation is deferred to a future phase. Options to explore:
- Witness expressions (Vegas expressions verified to satisfy the constraint)
- Polynomial time complexity bounds
- Enumerable domains (trivially tractable via enumeration)
- Decidable in a specific theory (SMT-friendly)

For the near-term, enumerable types provide both satisfiability AND tractability automatically.

### 6.2 Dynamic Unsatisfiability (Resolved)

**Design decision: Require satisfiability for ALL possible prior states.**

The constraint `where y != Alice.x` is satisfiable in general but may become unsatisfiable for specific Alice moves. The conservative approach:
- The compiler must prove satisfiability for ALL reachable game states
- If a constraint CAN become unsatisfiable for ANY valid sequence of prior moves, the value is typed `opt T`
- This is the strongest guarantee: fair-play is preserved regardless of opponent strategy

Rationale: If Alice can trap Bob into an impossible situation by strategic choice, that's unfair to Bob. The type system must reflect this possibility.

### 6.3 Who bears responsibility for intractable constraints?

If the game designer writes an intractable constraint:
- Should the compiler reject it? (Restrictive but safe)
- Should the compiler warn and require explicit acknowledgment? (Flexible but error-prone)
- Should the type system force `opt T` and let downstream code handle it? (This proposal)

### 6.4 How does this interact with subgames?

When control transfers to a subgame after "computational pass," what's the pool state? This needs integration with the subgame semantics in SUBGAMES.md.

---

## 7. Examples

### 7.1 Safe: Enumerable with Guaranteed Satisfiability

```
type door = {0, 1, 2}
yield Host(goat: door) where goat != Guest.d;
```
- Domain: 3 values
- For any `Guest.d ∈ {0,1,2}`, there exist 2 valid choices for `goat`
- **Type: `door` (non-optional)** - fair-play guaranteed

### 7.2 Unsafe: Enumerable but Possibly Unsatisfiable

```
type bit = {0, 1}
yield Alice(x: bit);
yield Bob(y: bit) where y != Alice.x && y != 1 - Alice.x;
```
- For any Alice move, Bob's constraint is unsatisfiable (excludes both values)
- **Type: `opt bit`** - fair-play NOT guaranteed

### 7.3 Unsafe: Infinite Domain

```
yield Alice(x: int) where x * x == 17;
```
- Unsatisfiable (17 is not a perfect square)
- **Type: `opt int`** - fair-play NOT guaranteed

### 7.4 Questionable: Satisfiable but Possibly Intractable

```
yield Alice(p: int, q: int) where isPrime(p) && isPrime(q) && p * q == N;
```
- Satisfiable (by construction of N as semiprime)
- Finding witnesses requires factoring
- **Type: `opt int × opt int`** - tractability NOT proven

### 7.5 Safe with Null Acceptance

```
yield Alice(x: int) where x > 100 || null;
```
- If the constraint allows null as a valid "non-answer," fair-play is preserved
- Alice can always produce null if no positive integer works
- **Type: `opt int`** - but this is acceptable by design

---

## 8. Summary

Fair-play liveness requires that honest players can always act. Where clauses threaten this by potentially creating impossible or intractable situations. The proposed solution:

### Design Principles

1. **Default to `opt T`** for values guarded by where clauses with unproven liveness
2. **Upgrade to `T`** only when conditions are proven:
   - **Near-term**: Universal satisfiability (for ALL reachable game states)
   - **Future**: Tractability via witness expressions (Vegas expressions verified to satisfy the constraint)
3. **Computational inability is distinct from strategic quit**:
   - Inability MUST NOT trigger quit handlers
   - Inability MUST NOT forfeit stakes
   - The type system must track the source of optionality

### Implementation Phasing

**Phase 1 (Near-term): Satisfiability validation**
- For enumerable types: leverage existing EFG infrastructure (`Semantics.kt` enumeration)
- Check that for ALL reachable game states, at least one value satisfies the where clause
- Straightforward implementation - mostly plumbing

**Phase 2 (Future): Tractability validation**
- Witness expressions: Vegas expressions that the compiler verifies always satisfy the where clause
- For enumerable types: trivially tractable (enumerate and pick first valid)
- For infinite types: require explicit witness or SMT-backed proof

### Key Insight

For enumerable types, both satisfiability and tractability come essentially "for free" from existing infrastructure. The game-theoretic enumeration already explores all states and filters by guards - surfacing this as a type-level guarantee requires minimal additional work.

This preserves the game-theoretic integrity of Vegas while ensuring fair treatment of cooperative players who are blocked by constraints beyond their control.

# Vegas Language Reference

## Overview

Vegas is a domain-specific language for specifying strategic games. It emphasizes **distribution transparency**, allowing developers to write game logic as a sequential specification while the compiler handles the complexities of distributed, adversarial execution.

## Execution Model: The Dependency DAG

Unlike traditional imperative languages that execute line-by-line, or round-based systems that execute in lock-step, Vegas compiles your program into a **Directed Acyclic Graph (DAG)** of actions. Internally this graph is called the **EventGraph** (matching the same name in the VegasCore Lean formalization); each surface-level action becomes a node in it.

### 1. Action Dependencies
The compiler analyzes data flow to determine dependencies. An action $B$ depends on action $A$ if:
- $B$ reads a variable written by $A$.
- $B$ is a `reveal` of a commitment made in $A$.
- $B$ uses a variable in a `where` clause that was written by $A$.

### 2. Concurrent Execution
Actions that do not depend on each other are considered **concurrent**.
- **In Analysis (Gambit)**: Concurrent actions are modeled as simultaneous moves (information sets), meaning players move without knowing the other's choice.
- **In Execution (Solidity)**: Concurrent actions can be submitted to the blockchain in any order.

### 3. Automatic Front-Running Protection
The compiler identifies "Risk Partners"—actions that are both **public** and **concurrent**. To prevent one player from seeing the other's move in the mempool and reacting (front-running), the compiler automatically rewrites these actions into a **Commit-Reveal** pattern.

**Original Code:**
```vegas
yield Alice(x: int);
yield Bob(y: int);
// If x and y are independent, Alice could wait to see y before sending x.
````

**Compiled DAG Behavior:**

1.  Alice commits `hash(x)`.
2.  Bob commits `hash(y)`.
3.  Alice reveals `x`.
4.  Bob reveals `y`.

## Language Syntax

### Macros

Vegas supports hygienic macros to encapsulate reusable logic. Macros are inlined before the intermediate representation (IR) is generated.

```vegas
// Define a macro
macro isWinner(guess: int, target: int): bool = guess == target;

// Use the macro
yield Player(g: int);
withdraw isWinner(Player.g, 5) ? ...
```

### Game Flow

#### `join`

Players enter the game. This is implicitly the root of the DAG.

```vegas
join Alice() $ 100; // Join with 100 wei deposit
```

#### `yield`

A player provides information.

```vegas
yield Alice(x: int);           // Public move
yield Bob(y: hidden int);      // Hidden move (generates commitment)
```

#### `reveal`

A player opens a previously hidden value.

```vegas
reveal Bob(y: int);
```

*Note: Constraints (where clauses) on hidden values are checked during the `reveal` phase, not the `yield` phase.*

#### `withdraw`

Specifies the terminal payouts. This runs once all necessary actions are complete or players have timed out.

A `withdraw` outcome may contain `burn N` items alongside `Role -> Exp`
items. `burn` represents funds that leave the strategic pot without
going to any role: the principled accounting for branches where the
role payouts do not total the deposits.

```vegas
withdraw P.guess == Sample.w
  ? { P -> 100 }
  : { P -> 0; burn 100 }
```

The compiler verifies pot conservation at every reachable terminal of
the strategic game tree (Pass E): `sum(role payouts) + burn` must
equal `sum(deposits)`. Branches that underpay (funds stuck) or overpay
(contract reverts) are rejected with a `ConservationViolation`.

#### `random` (Nature actor)

A `random Role;` declaration introduces a Nature-modeled participant.
Concrete trust model:

- The role has an actor identity (an EVM address) so it can perform
  private actions (`commit` / `reveal`). Whoever first calls
  `join_Role()` claims the role.
- Every `commit` / `yield` / `reveal` by the role is sample-modeled
  (analysis treats the value as a draw from the declared distribution,
  defaulting to uniform over the parameter type if no `~ D` is given).
- The role does not appear in `withdraw` payouts. `~ D` is an
  *analysis assumption*, not a contract-level enforcement: the actor
  is **trusted** to follow the stated distribution. The on-chain
  contract emits standard commit/reveal scaffolding bound by
  `msg.sender` checks; it does not police whether the submitted
  values look uniform.
- `random` actors cannot quit, are not penalized on misbehavior, and
  have no automatic recourse if a reveal fails the declared support.
  A real-world deployment is expected to assign the actor's address
  to a trusted oracle, an off-chain MPC committee, or similar.

#### `sample` (anonymous public draw)

A `sample (x: T ~ D);` binding introduces an anonymous public draw
under the reserved label `Sample`. Concrete trust model:

- No actor identity; the value is computed on-chain from
  `block.prevrandao` (the chain's RANDAO beacon). Anyone may call the
  generated function; the value depends on the proposer's beacon, not
  the caller.
- `~ D` is allowed but currently only `uniform` priors are
  implementable at the EVM level (rejection sampling for non-uniform
  is future work). Non-uniform priors compile for analysis (Gambit,
  MAID) but EVM emission rejects them.
- References use `Sample.x` in expressions.

#### Distribution annotation `~ D` on strategic actions

A `commit P1(x: int ~ uniform { 0, 1, 2 })` on a *strategic* role is
an **analysis assumption**: the analysis treats the action as a chance
draw from D, and assumes the actor plays through (commit followed by
reveal, no quit). It has no operational effect; the EVM contract still
gates by `msg.sender` and accepts any value within the declared support.
The annotation tells Gambit / MAID / PRISM how to model the actor for
analysis, and `where` clauses are interpreted as standard probabilistic
conditioning (`D | phi`).

### Types

- `int`: Unbounded integer (mapped to `int256`).
- `bool`: Boolean value.
- `address`: Ethereum address.
- `type T = {1, 2, 3}`: Enumerated subset.
- `type T = {1..10}`: Range.

## Concrete Semantics (Blockchain)

The abstract DAG is compiled into a Solidity contract that enforces the game rules.

### 1. The `depends` Modifier

The generated contract does not use a global "step" counter. Instead, every action is gated by a `depends` modifier:

```solidity
modifier depends(Role r, uint id) { ... }
```

An action can be performed only if all its ancestors in the DAG are marked as `done`.

### 2. Timeout and Bailing

Vegas implements a **non-blocking timeout** mechanism to prevent griefing (where one player stops moving to freeze the funds).

- **Global Timeout**: If a player fails to act within `TIMEOUT` seconds of their dependencies being met, any other player can trigger a check.
- **Bail State**: The non-responsive player is marked as `bailed`.
- **Fall-Through**: The `depends` modifier is relaxed. If an action depends on a player who has `bailed`, that dependency is ignored. The game proceeds as if the value were `null`.

### 3. Null Handling

Because any player might bail, all variable reads are potentially nullable (`Opt[T]`). The `withdraw` clause must explicitly handle these cases:

```vegas
withdraw (Alice.x != null) 
    ? { Alice -> 10 } 
    : { Alice -> -10 } // Penalty for bailing
```

## Compilation Pipeline

1.  **Parsing & Type Checking**: Validates types and macro expansions.
2.  **Macro Inlining**: Desugars macros into raw expressions.
3.  **DAG Construction**:
    - Builds the dependency graph.
    - Identifies "Risk Partners" (concurrent public moves).
    - **Rewrites DAG**: Inserts Commit and Reveal nodes for risk partners.
4.  **Backend Generation**:
    - **Solidity**: Generates functions with `depends` modifiers and bail logic.
    - **Gambit**: Generates a game tree where concurrent DAG nodes share information sets.

## Related langauges

https://github.com/marlowe-lang


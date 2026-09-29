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
4.  Bob reveals `y`, after Alice's opening (or her deadline).

The commitments are simultaneous; the openings are not. A reveal is a public
event, and on an asynchronous ledger whoever opens later has already seen the
earlier openings when deciding whether to open. The compiler therefore orders
the openings of one statement in source order, and the analysis model gives
the later revealer that information. A `reveal` statement naming several roles
opens in the order written, the same way.

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

Joining is a precondition of the game, not a move within it: it cannot be
quit and takes no handler. If a role has not joined by its deadline, the
instance is aborted and every deposit is refunded.

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

- No actor identity and no entry point. The contract is deployed with a
  randomness beacon (`IVegasBeacon`); its value is fixed by the first
  beacon round published `BEACON_DELAY` after the draw's node becomes
  ready. The delay outlasts the chain's finality, so the block that made
  the draw ready is final before anyone can know the round. Nobody chooses
  when it is drawn or what it is, and no player can withhold it: any later
  call settles it.
- The beacon must be unpredictable, unbiased and live, and nobody may see a
  round before it is published. A threshold beacon (drand) meets this under
  its threshold assumption; a VRF service's operator sees each output first
  and is trusted not to withhold one. Block-derived values do not qualify:
  whoever triggers a block-derived draw can retry until it suits them.
- `~ uniform { ... }` and `~ weighted { ... }` are both implemented on
  chain, by reducing the beacon output modulo the weights' common
  denominator (bias below `D / 2^256`).
- References use `Sample.x` in expressions.

#### `sample Role(...)` (private draw) and `utility`

`sample Role(x: T ~ D);` draws a value for a strategic role that only
that role observes: its private type, in the game-theoretic sense (a
bidder's valuation, a player's hand). `~ D` may be omitted when `T` is
finite, meaning uniform over `T`. The role must already have joined.

- The draw belongs to the analysis alone. Nature makes it; the owner
  observes it; the other roles never do. The owner's later decisions
  are made knowing it (Gambit information sets, MAID information edges),
  and in DQBF it is universally quantified even inside the coalition.
- Nothing about it reaches the contract, the Scribble protocol or a
  channel: it has no transaction, commitment or message, and the
  schedule contracts through it. The Lightning backend refuses it.
- No `where` clause and no `withdraw` can read it, since the contract
  could not evaluate them. A private type affects money only through
  the owner's choices.
- Its only reader is a `utility` clause after `withdraw`, which gives
  each strategic role its analysis utility:

  ```vegas
  withdraw (A.b >= B.b) ? { Seller -> A.b; A -> 2 - A.b; B -> 2 }
                        : { Seller -> B.b; A -> 2; B -> 2 - B.b }
  utility {
      A -> (A.b != null && B.b != null && A.b >= B.b) ? A.payout - 2 + A.v : A.payout - 2;
      B -> (A.b != null && B.b != null && A.b < B.b) ? B.payout - 2 + B.v : B.payout - 2;
      Seller -> Seller.payout;
  }
  ```

  A utility may read every field in scope, private draws included, and
  `Role.payout`, that role's settlement under the `withdraw` (so the
  name `payout` is reserved). Fields a role could quit before setting
  are optional here, as in `withdraw`. A role without a utility gets its
  payout net of its deposit, which is also the default when there is no
  clause. Pot conservation is checked on the settlement, never on the
  utilities.

See `examples/PrivateValueAuction.vg`.

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

### 1. The Schedule

The generated contract does not use a global "step" counter. It holds the
event graph as a table (each node's owner and predecessors, in topological
order) and records, per node, when it became ready and when it was resolved.
A move is accepted only while its node is ready and unresolved:

```solidity
function move_Host_2(bytes32 _hidden_car) public {
    _beginMove(2, Role.Host);   // settle, then: caller's role, ready, still open
    ...
    _endMove(2);
}
```

### 2. Deadlines and Quitting

Vegas implements a **non-blocking timeout** mechanism to prevent griefing (where one player stops moving to freeze the funds).

- **Readiness**: A node is ready once every predecessor is resolved; its readiness time is the latest predecessor resolution.
- **Deadline**: A ready node that is not played within `TIMEOUT` seconds of its readiness expires at that deadline, and its owner quits. Only a ready node can expire, so a player is never blamed for a move it could not yet make, and a move after its own deadline is rejected.
- **Persistent quit**: A role that quit has no further moves; its later nodes resolve without a value, as in the analysis model.
- **Settlement**: Anyone may call `settle()` to resolve what can be resolved; every move and withdrawal settles first. A role that quit can still withdraw what the `withdraw` clause assigns it.

### 3. Null Handling

A field written under a `|| null` handler is nullable (`opt T`) and the `withdraw` clause must handle the missing case. A `where` guard that reads another role's field is discharged when that field is missing: it holds vacuously, and no value is invented for it.

```vegas
withdraw (Alice.x != null) 
    ? { Alice -> 10 } 
    : { Alice -> -10 } // Penalty for quitting
```

## Compilation Pipeline

1.  **Parsing & Type Checking**: Validates types and macro expansions.
2.  **Macro Inlining**: Desugars macros into raw expressions.
3.  **DAG Construction**:
    - Builds the dependency graph.
    - Identifies "Risk Partners" (concurrent public moves).
    - **Rewrites DAG**: Inserts Commit and Reveal nodes for risk partners.
4.  **Backend Generation**:
    - **Solidity**: Generates the schedule, one entry point per move, and per-role withdrawals; optionally a terminal audit (see `docs/AUDITED-RUNTIME.md`).
    - **Gambit**: Generates a game tree where concurrent DAG nodes share information sets.

## Related languages

https://github.com/marlowe-lang


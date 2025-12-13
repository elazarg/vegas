# Vegas DAG & Proof-Game Design

**Status:** Draft, but intended as a stable design spine
**Scope:** How Vegas uses DAGs, values, and properties to define protocol semantics and backends (Solidity, Gambit, SMT).
**Assumption:** Vegas remains a research codebase; we optimize for clarity and evolvability, not backward compatibility.

**Related Documents:**
- `DAG_INTEGRATION_PLAN.md` - ADR documenting the witness/property semantic model and architectural decisions
- This document (DESIGN.md) - Detailed implementation specification and testing strategy

---

## 1. High-Level Picture

### 1.1 Vegas in One Sentence

Vegas is a **protocol DSL** that compiles to:

* a **Dependency DAG of actions** (semantic/structural core),
* a **Solidity implementation** (on-chain protocol),
* and an **Extensive-Form Game (EFG)** (for analysis in Gambit etc.).

For a fixed Vegas program:

> Vegas program → IR → `ActionDag` (Dependency DAG) →
> (a) Solidity contract,
> (b) EFG (Gambit),
> (c) optional SMT/DQBF encodings.

### 1.2 Node / Action View

Semantically, each action is:

* A **concrete move**: picks actual values (ints/bools/etc.) for parameters.
* A **bundle of properties** about the protocol state that become true at that point.
* Annotated with **visibility** (COMMIT/REVEAL/PUBLIC) that controls what is known when.

We already treat values as “simple proofs”:

* choosing `x` such that `φ(x)` holds *is* a proof of `∃x. φ(x)` at the semantic level,
* we do **not** make structured proof terms first-class game objects (for now).

---

## 2. Semantic Stance: Intensional Values, Extensional Proofs

We distinguish three levels:

1. **Value-level intensionality (current, core):**

    * Each action chooses **concrete values**.
    * Later guards, visibility, payoffs depend on those exact values.
    * Different values with the same high-level “meaning” are still different moves.

2. **Property-bundle intensionality (current, needs clearer modeling):**

    * Each action introduces a **bundle of properties**:

        * domain/guard constraints,
        * equality/consistency facts (commit ↔ reveal),
        * arbitrary `where` clauses.
    * Different ways of “proving the same headline thing” can expose **different bundles**, and later behaviour can depend on which bundle was established.

3. **Proof-object intensionality (future / optional):**

    * We do **not** (currently) model structured proofs or implementations as separate game resources.
    * No moves of the form “apply a transformation to your proof term”.

**Design decision (for now):**

* Core semantics is:

    * **intensional on concrete values** (moves choose values),
    * **extensional on proofs** (we track the *facts* they establish, not their internal derivation),
    * with a **rich property-bundle layer** to capture “how” a fact was established insofar as it affects observable properties.

This matches the way Vegas already works with commit/reveal and `where` clauses, but makes the intent explicit.

---

## 3. Core Data Structures

### 3.1 ActionId

We keep ActionIds simple and IR-oriented:

```kotlin
typealias ActionId = Pair<RoleId, Int> // (Role, StepIndex - source sequence number)
```

* `RoleId` = logical participant.
* `Int` = original step index in IR (a stable identifier from the source definition).

This can be refined later (e.g. adding a local action index) without changing the DAG API.

### 3.2 ActionMeta and ActionStruct

Metadata describes **who**, **what**, and **how visible**. In the implementation (`ActionDag.kt`), this is split into `ActionMeta` (container) and `ActionStruct` (structural visibility):

```kotlin
data class ActionStruct(
    val owner: RoleId,
    val writes: Set<FieldRef>,            // fields produced/updated
    val visibility: Map<FieldRef, Visibility>,
    val guardReads: Set<FieldRef>         // fields read in guards/where
)

enum class Visibility {
    COMMIT,   // hidden committed value
    REVEAL,   // reveals committed value
    PUBLIC    // plain public value, no prior commit
}
```

Interpretation:

* Every action:

    * **writes** some fields (new or updated).
    * **reads** some fields in guards/where clauses.
    * has visibility for each written field:

        * COMMIT: hidden but bound to a future reveal,
        * REVEAL: makes a previously committed value public / checkable,
        * PUBLIC: straight public assignment.

This is the **property-bundle hook**: the semantics of “what becomes true” is driven by `writes`, `visibility`, and the IR’s `where` clauses.

### 3.3 ActionDag (Dependency DAG)

`ActionDag` wraps a generic `Dag<ActionId>` with metadata and reachability info:

```kotlin
class ActionDag private constructor(
    private val dag: Dag<ActionId>,
    private val payloads: Map<ActionId, ActionMeta>,
    private val reach: Reachability<ActionId>
) : Dag<ActionId> by dag {

    fun meta(id: ActionId): ActionMeta = payloads.getValue(id)

    fun owner(id: ActionId): RoleId = meta(id).struct.owner
    fun writes(id: ActionId): Set<FieldRef> = meta(id).struct.writes
    fun visibilityOf(id: ActionId): Map<FieldRef, Visibility> = meta(id).struct.visibility
    // ...

    /** Convenience: can these actions run without ordering constraints? */
    fun canExecuteConcurrently(a: ActionId, b: ActionId): Boolean =
        !reach.comparable(a, b) // Implementation uses precomputed reachability

    companion object {
        fun fromGraph(
            nodes: Set<ActionId>,
            deps: Map<ActionId, Set<ActionId>>,
            payloads: Map<ActionId, ActionMeta>,
        ): ActionDag? {
            // Checks acyclicity and visibility invariants
            // Returns null if invalid
        }
    }
}
```

This means:

* All DAG algorithms (`topo`, `prerequisitesOf`, `dependentsOf`, slicing) remain reusable.
* Additional constraints (commit–reveal ordering, visibility) are centralized in `fromGraph(…)`.

### 3.4 DAG Invariants

Any `ActionDag` must satisfy:

1. **Acyclicity:**

    * No cycles in `prerequisitesOf`.
    * Enforced by `ExplicitDag.from(…, checkAcyclic = true)`.

2. **Commit → Reveal ordering:**

    * For each field with a COMMIT and REVEAL action:

        * the COMMIT must be a predecessor of the REVEAL in the DAG.

3. **Visibility for reads:**

    * If action `a` reads field `f` (in guards/where), then:

        * either `f` is PUBLIC and written before `a`, or
        * `f` is COMMIT before a REVEAL before `a`, or
        * there is an explicit modelled mechanism for reading hidden values (currently: **disallowed**).

   Currently we enforce:

   > Actions can only read fields that are either PUBLIC or already REVEALed in some predecessor.

These invariants model the all-or-nothing, on-chain commit–reveal pattern.

---

## 4. Building the Dependency DAG from IR

**File:** `src/main/kotlin/vegas/ir/ActionDag.kt`

We derive `ActionDag` from `GameIR`:

1. **Collect nodes:**

    * For each source index `i` and each role `r` that has an action at that index, create `ActionId(r, i)`.

2. **Infer dependencies:**

   For each action `A = (r, i)`:

    * **Data dependencies (guard captures):**
      For each `fieldRef` appearing in `requires.captures` or `where`:

        * find the latest prior action that writes `fieldRef` (by index);
        * add an edge from that action to `A`;
        * if the field is COMMIT/REVEAL, ensure the REVEAL is also a predecessor of `A`.

    * **Commit–reveal:**

        * If `A` is a REVEAL for some committed field `f`, add edge from COMMIT(f) → `A`.

3. **Build metadata:**

   For every `ActionId(r, i)`:

    * `role = r`
    * `writes = set of FieldRef` derived from the action’s signature / IR.
    * `visibility[f]` determined by commit/reveal detection.
    * `guardReads` from captures/conditions in the IR.

4. **Construct DAG:**

   ```kotlin
   return ActionDag.fromGraph(
       nodes = actions,
       deps = dependencies,
       payloads = payloads
   )
   ```

5. **Failure behavior:**

    * If acyclicity or visibility invariants fail, `fromGraph` returns `null`.
    * The type checker should surface this as a **static error**:

        * “Invalid dependency structure (cycle or visibility violation).”

---

## 5. Backends Using the DAG

### 5.1 Solidity Backend: DAG-Based Scheduling

**Goal:** No global state variable for execution steps, no barrier synchronization. Dependencies expressed as per-action preconditions.

**File:** `src/main/kotlin/vegas/backend/evm/GameToEvmIR.kt`

Outline:

1. **Linearize DAG (deterministic IDs):**

   ```kotlin
   private fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
       dag.topo()
          // Stable deterministic ordering: by index, then role name
          // (arbitrary but consistent across compilations)
          .sortedWith(compareBy({ it.second }, { it.first.name }))
          .mapIndexed { idx, id -> id to idx }
          .toMap()
   ```

   Used for:

    * `uint constant ACTION_X = k;`
    * `mapping(uint => bool) actionDone;`

2. **Per-action function generation:**

   For each `actionId` in `dag.topo()`:

    * Gather prerequisites `dag.prerequisitesOf(actionId)`.

    * Generate Solidity function:

      ```solidity
      function move_Role_seq(...)
          external
          by(Role)
          notDone(ACTION_FOO)
          depends(ACTION_bar)
          depends(ACTION_baz)
      {
          // payload logic
          actionDone[ACTION_FOO] = true;
          actionTimestamp[ACTION_FOO] = block.timestamp;
      }
      ```

    * Payload logic includes:

        * commit (store hashes),
        * reveal (check hashes, enforce where clauses),
        * public updates.

3. **Modifiers:**

   ```solidity
   modifier depends(uint actionId) {
       require(actionDone[actionId], "dependency not satisfied");
       _;
   }

   modifier notDone(uint actionId) {
       require(!actionDone[actionId], "already done");
       _;
   }
   ```

4. **Timeouts (later):**

    * Timeouts become relative to the max timestamp of prerequisites:

        * `T_max = max(actionTimestamp[dep] for dep in prereqs)`
        * require `block.timestamp <= T_max + duration`.

   Implementation deferred but structurally supported by storing `actionTimestamp`.

### 5.2 Gambit Backend: EFG with DAG-Derived Info Sets

**Goal:** EFG reflects:

* true simultaneity: actions that can execute concurrently (no path) are potential simultaneous moves;
* knowledge: what each role knows, based on `visibility` and DAG.

**Approach:**

* `FrontierMachine<ActionId>` maintains the set of currently enabled actions (all prerequisites done).
* For each frontier:

    * group enabled actions by owner,
    * for a given role:

        * its decision node includes only its enabled actions,
        * its information set is determined by:

            * which fields it knows (public or previously revealed),
            * which paths are indistinguishable under that visibility model.

**Implementation sketch:**

```kotlin
class DagGameTreeBuilder(ir: GameIR, dag: ActionDag) {
    fun build(): GameTree {
        val frontier = FrontierMachine(dag)
        return buildFromFrontier(frontier, State.empty())
    }
    // ...
```

Implementation uses:

* `ActionDag` metadata (guardReads and visibility),
* `Algo.ancestorsOf` for transitive closure of known fields,
* plus current state to determine what each role knows at each node.

### 5.3 SMT/DQBF Backend

**Goal:** Provide two distinct verification views of the game using SMT-LIB 2.0.

1.  **Satisfiability (QF-SMT):**
    *   **Purpose:** Check for existence of a single valid trace (e.g. "Can state X ever be reached?").
    *   **Encoding:** Flat global constants (`(declare-const ...)`).
    *   **Dependencies:** Asserted via boolean guards (`action_done => prereqs_done`).
    *   `Hidden` values are treated as existential variables (unconstrained by others' knowledge in a single trace).

2.  **Strategy Synthesis (DQBF / Skolemized):**
    *   **Purpose:** Check for existence of *strategies* (winning/valid) for roles.
    *   **Encoding:** Skolem functions (`(declare-fun move (Observed ...) Type)`).
    *   **Dependencies:**
        *   Each action's value depends *only* on the information visible to the owner at that time (the "dependency set").
        *   Dependency Set = Public/Revealed priors + Owner's own past moves.
        *   This effectively encodes DQBF-style dependencies ($\forall \text{inputs} \exists \text{strategy}$).
    *   **Hidden/Opaque:**
        *   `Hidden(val)` is a function of the owner's knowledge (including private history).
        *   Other roles' moves cannot depend on it until `Reveal`.

**CLI Integration:**
*   `vegas smt` defaults to QF-SMT.
*   `vegas smt --dqbf` (or similar flag) generates the strategy-aware encoding.

---

## 6. Testing Strategy (Important!)

DAG is core infrastructure and **must** be well-tested.

### 6.1 Unit Tests for DAG Construction

**Files:** `src/test/kotlin/vegas/ActionDagCoreTest.kt`, `src/test/kotlin/vegas/ActionDagFromIrTest.kt`

Tests:

1. **Basic examples build a DAG:**

    * For each example game (`MontyHall.vg`, `OddsEvens.vg`, `Prisoners.vg`, …):

        * parse → IR → `compileToIR(ast).dag`,
        * assert non-null,
        * assert `dag.nodes` non-empty.

2. **Commit–reveal ordering:**

    * For each example with commits/reveals:

        * find actions whose `visibility[f] == COMMIT` and `== REVEAL`,
        * assert `dag.reaches(commit, reveal)` (transitive reachability).

3. **Visibility on reads:**

    * Introduce a small invalid IR where an action reads a hidden field before reveal:

        * ensure DAG construction returns `null` or fails with a clear error.

4. **Cycle detection:**

    * Construct a synthetic graph where A depends on B and B depends on A.
    * Ensure DAG construction fails.

5. **Concurrent-execution detection:**

    * Example like `OddsEvens` where two players move independently:

        * find `oddMove`, `evenMove`,
        * assert `dag.canExecuteConcurrently(oddMove, evenMove)`.

6. **Topological order correctness:**

    * For `topo = dag.topo()`:

        * ensure there is no edge `u → v` with `index(u) > index(v)`.

### 6.2 Solidity Integration Tests

**File:** `src/test/kotlin/vegas/GoldenMasterTest.kt`

For each example game:

1. Build IR → DAG → Solidity.

2. Assert:

    * There is no `phase` state variable in the generated Solidity.
    * `ACTION_…` constants exist and are stable on repeated compilations.
    * Every action function:

        * has `notDone` modifier,
        * has `depends` for all DAG prerequisites.

3. (Optional, but valuable): feed generated Solidity to `solc` in test harness and assert compilation success.

### 6.3 Gambit/EFG Tests

**File:** `src/test/kotlin/vegas/GambitSemanticTest.kt`

* For small examples, generate EFG via DAG backend and check:

    * Number of information sets matches expectations.
    * Actions that are independent in the DAG appear simultaneous / in same info set where appropriate.

### 6.4 Property-Based Tests (Optional, Future)

* Generate random small DAGs (with synthetic `ActionMetadata`) and check:

    * `topo()` respects ordering.
    * `canExecuteConcurrently` matches graph properties.
    * Random IRs are either rejected with clear errors or produce DAGs satisfying invariants.

---

## 7. Parametric / Future Decisions (Explicitly Deliberate)

These are **axes**, not yet implemented. This doc keeps the current design compatible with all reasonable choices.

1. **Richer property layer:**

    * Today: properties live implicitly in IR `where`/guards.
    * Future: `Prop(expr, kind: GUARD | ASSERTION | ORACLE_BACKED)` inside `ActionMeta`.

2. **Crypto / oracle modeling:**

    * Today: commit–reveal is modeled structurally; other proofs are an implementation detail.
    * Future: add abstract predicates like `ValidProof(p, y, x)` to represent oracle-checked properties.

3. **Per-player knowledge:**

    * Today: PUBLIC/REVEAL = visible to everyone; no full epistemic model.
    * Future: per-role visibility, or a separate visibility DAG.

4. **Proof objects as resources:**

    * Today: **no** explicit proof terms in game state.
    * Future: if needed, add a second layer where proofs/implementations are first-class and manipulable.

5. **Vegas ↔ K-FOG alignment:**

    * Today: loose; Vegas generates EFGs + DAGs, K-FOG is a more general theory.
    * Future: formal embedding of Vegas games into a fragment of K-FOG.

---

## 8. Summary

* Vegas’ **core semantic object** is `ActionDag` (a `Dag<ActionId>`) annotated with `ActionMeta` (role, writes, visibility, reads).
* We are **already intensional** at value level: actions choose concrete values that matter later.
* We deliberately stay **extensional** at proof-object level: we track **which facts are established**, not how proofs are structured.
* The **property-bundle view** (what each node makes true and visible) is the main lever for expressing:

    * adversarial exploitation of specific implementations,
    * architectural coupling in software terms.
* The **DAG** is the structural backbone used by all backends (Solidity, Gambit, SMT) and must be **well-tested**.

This document is meant to stay close to the code and guide incremental changes. Adding or changing theory (K-FOG, solution concepts, query logics) should work *with* this spine, not against it.

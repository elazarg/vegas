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

> Vegas program → IR → `DependencyDag<ActionId>` →
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
typealias ActionId = Pair<RoleId, Int> // (Role, StepIndex - original IR phase, not semantic phase)
```

* `RoleId` = logical participant.
* `Int` = original phase index in IR (even though we are moving away from phase *semantics*, the index is a useful stable identifier).

This can be refined later (e.g. adding a local action index) without changing the DAG API.

### 3.2 ActionMetadata

Metadata describes **who**, **what**, and **how visible**:

```kotlin
data class ActionMetadata(
    val role: RoleId,
    val writes: Set<FieldRef>,            // fields produced/updated
    val visibility: Map<FieldRef, Visibility>,
    val guardReads: Set<FieldRef>         // fields read in guards/where
    // NOTE: placeholder: later we may add explicit Prop bundles here
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

### 3.3 DependencyDag

`DependencyDag` wraps a generic `Dag<T>` with metadata:

```kotlin
class DependencyDag<T : Any> private constructor(
    private val underlying: Dag<T>,
    private val meta: Map<T, ActionMetadata>
) : Dag<T> by underlying {

    fun metadata(action: T): ActionMetadata = meta[action]!!

    fun owner(action: T): RoleId = metadata(action).role
    fun writes(action: T): Set<FieldRef> = metadata(action).writes
    fun visibility(action: T): Map<FieldRef, Visibility> = metadata(action).visibility
    fun guardReads(action: T): Set<FieldRef> = metadata(action).guardReads

    /** Convenience: can these actions run without ordering constraints? */
    fun canExecuteConcurrently(a: T, b: T): Boolean =
        !Algo.reaches(a, b, ::prerequisitesOf) &&
        !Algo.reaches(b, a, ::prerequisitesOf)

    companion object {
        fun <T : Any> from(
            nodes: Set<T>,
            prerequisitesOf: (T) -> Set<T>,
            metadata: (T) -> ActionMetadata
        ): DependencyDag<T>? {
            val dag = ExplicitDag.from(nodes, prerequisitesOf, checkAcyclic = true)
                ?: return null
            val metaMap = nodes.associateWith(metadata)

            if (!isValidVisibilityStructure(dag, metaMap)) return null

            return DependencyDag(dag, metaMap)
        }

        private fun <T : Any> isValidVisibilityStructure(
            dag: Dag<T>,
            meta: Map<T, ActionMetadata>
        ): Boolean {
            // See invariants in §3.4
            // Implementation is straightforward: walk edges, check ordering & reads
            return checkCommitRevealOrdering(dag, meta) &&
                   checkVisibilityOnReads(dag, meta)
        }
    }
}
```

This means:

* All DAG algorithms (`topo`, `prerequisitesOf`, `dependentsOf`, slicing) remain reusable.
* Additional constraints (commit–reveal ordering, visibility) are centralized in `from(…)`.

### 3.4 DAG Invariants

Any `DependencyDag` must satisfy:

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

We derive `DependencyDag<ActionId>` from `GameIR`:

1. **Collect nodes:**

    * For each phase index `p` and each role `r` that has an action in that phase, create `ActionId(r, p)`.

2. **Infer dependencies:**

   For each action `A = (r, p)`:

    * **Data dependencies (guard captures):**
      For each `fieldRef` appearing in `requires.captures` or `where`:

        * find the latest prior action that writes `fieldRef` (by phase index);
        * add an edge from that action to `A`;
        * if the field is COMMIT/REVEAL, ensure the REVEAL is also a predecessor of `A`.

    * **Commit–reveal:**

        * If `A` is a REVEAL for some committed field `f`, add edge from COMMIT(f) → `A`.

3. **Build metadata:**

   For every `ActionId(r, p)`:

    * `role = r`
    * `writes = set of FieldRef` derived from the action’s signature / IR.
    * `visibility[f]` determined by commit/reveal detection.
    * `guardReads` from captures/conditions in the IR.

4. **Construct DAG:**

   ```kotlin
   return DependencyDag.from(
       nodes = actions,
       prerequisitesOf = { dependencies[it].orEmpty() },
       metadata = ::buildMetadata
   )
   ```

5. **Failure behavior:**

    * If acyclicity or visibility invariants fail, `from` returns `null`.
    * The type checker should surface this as a **static error**:

        * “Invalid dependency structure (cycle or visibility violation).”

---

## 5. Backends Using the DAG

### 5.1 Solidity Backend: DAG-Based Scheduling

**Goal:** No phase variable, no barrier synchronization. Dependencies expressed as per-action preconditions.

**File (new):** `vegas/backend/solidity/DagBasedFromIR.kt`

Outline:

1. **Linearize DAG (deterministic IDs):**

   ```kotlin
   fun linearizeDag(dag: DependencyDag<ActionId>): Map<ActionId, Int> =
       dag.nodes
          // Stable deterministic ordering: by phase index, then role name
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
      function move_Role_phase(...) 
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

    * Payload logic is derived from the old phase-based backend:

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
class DagGameTreeBuilder(ir: GameIR, dag: DependencyDag<ActionId>) {
    fun build(): GameTree {
        val frontier = FrontierMachine(dag)
        return buildFromFrontier(frontier, State.empty())
    }

    private fun buildFromFrontier(frontier: FrontierMachine<ActionId>, state: State): GameTree {
        if (frontier.isComplete()) return Terminal(evaluatePayoffs(state))

        val enabled = frontier.enabled()
        val byRole = enabled.groupBy { dag.owner(it) }

        // For each role, compute known fields from transitive predecessors
        val (role, actions) = byRole.entries.first()
        val knownFields = computeKnownFields(actions, dag)
        val infoset = state.restrictTo(knownFields)

        // Build choice node...
    }

    private fun computeKnownFields(actions: List<ActionId>, dag: DependencyDag<ActionId>): Set<FieldRef> {
        // Get ALL predecessors (transitive closure), not just immediate
        val allPreds = actions.flatMap { action ->
            Algo.ancestorsOf(setOf(action), dag.nodes, dag::prerequisitesOf)
        }.toSet()

        // Fields are known if revealed by any predecessor
        return allPreds.flatMap { pred ->
            dag.visibility(pred).filterValues { it != Visibility.COMMIT }.keys
        }.toSet()
    }
}
```

Implementation uses:

* `DependencyDag.guardReads` and `visibility`,
* `Algo.ancestorsOf` for transitive closure of known fields,
* plus current state to determine what each role knows at each node.

### 5.3 SMT/DQBF Backend (Future)

Mapping:

* Each action’s decision variable depends only on predecessor variables in the DAG.
* DQBF style: `∃x(deps_x) ...` where `deps_x` = fields in `guardReads` / causal ancestors.

This is future work but structurally supported by `DependencyDag`.

---

## 6. Testing Strategy (Important!)

DAG is core infrastructure and **must** be well-tested. Current status: this is **not** done yet; this section defines the minimal required tests.

### 6.1 Unit Tests for DAG Construction

**File:** `src/test/kotlin/vegas/DagTest.kt`

Tests:

1. **Basic examples build a DAG:**

    * For each example game (`MontyHall.vg`, `OddsEvens.vg`, `Prisoners.vg`, …):

        * parse → IR → `buildDependencyDag(ir)`,
        * assert non-null,
        * assert `dag.nodes` non-empty.

2. **Commit–reveal ordering:**

    * For each example with commits/reveals:

        * find actions whose `visibility[f] == COMMIT` and `== REVEAL`,
        * assert `Algo.reaches(commit, reveal, dag::prerequisitesOf)` (transitive reachability, not just immediate prerequisites).

3. **Visibility on reads:**

    * Introduce a small invalid IR where an action reads a hidden field before reveal:

        * ensure `buildDependencyDag` returns `null` or fails with a clear error.

4. **Cycle detection:**

    * Construct a synthetic `GameIR` where A depends on B and B depends on A.
    * Ensure DAG construction fails (null) and type checker surfaces a cycle error.

5. **Concurrent-execution detection:**

    * Example like `OddsEvens` where two players move independently:

        * find `oddMove`, `evenMove`,
        * assert `dag.canExecuteConcurrently(oddMove, evenMove)`.

6. **Topological order correctness:**

    * For `topo = dag.topo()`:

        * ensure there is no edge `u → v` with `index(u) > index(v)`.

### 6.2 Solidity Integration Tests

**File:** `src/test/kotlin/vegas/SolidityDagTest.kt`

For each example game:

1. Build IR → DAG → Solidity (Dag-based backend).

2. Assert:

    * There is no `phase` state variable in the generated Solidity.
    * `ACTION_…` constants exist and are stable on repeated compilations.
    * Every action function:

        * has `notDone` modifier,
        * has `depends` for all DAG prerequisites.

3. (Optional, but valuable): feed generated Solidity to `solc` in test harness and assert compilation success.

### 6.3 Gambit/EFG Tests

**File:** `src/test/kotlin/vegas/GambitDagTest.kt`

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
    * Future: `Prop(expr, kind: GUARD | ASSERTION | ORACLE_BACKED)` inside `ActionMetadata`.

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

* Vegas’ **core semantic object** is a `DependencyDag<ActionId>` annotated with `ActionMetadata` (role, writes, visibility, reads).
* We are **already intensional** at value level: actions choose concrete values that matter later.
* We deliberately stay **extensional** at proof-object level: we track **which facts are established**, not how proofs are structured.
* The **property-bundle view** (what each node makes true and visible) is the main lever for expressing:

    * adversarial exploitation of specific implementations,
    * architectural coupling in software terms.
* The **DAG** is the structural backbone used by all backends (Solidity, Gambit, SMT) and must be **well-tested**.

This document is meant to stay close to the code and guide incremental changes. Adding or changing theory (K-FOG, solution concepts, query logics) should work *with* this spine, not against it.

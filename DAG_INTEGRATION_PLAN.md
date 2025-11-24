# Vegas DAG Integration – Stepwise Plan

**Goal:** Replace phase-based scheduling with DAG-based action dependencies in small, working increments.

**Key stance**

* We specialize to an **`ActionDag`**: a DAG over `ActionId`.
* We keep the existing generic graph primitives (`Dag<T>`, `ExplicitDag`) as infrastructure only.
* At each step:

    * the code builds and runs,
    * tests pass,
    * and the new piece is actually used (or at least reachable via CLI/API).

---

## Step Dependencies

```text
Step -1: Environment check
   ↓
Step 0: Baseline verification
   ↓
Step 1: ActionDag in isolation (types + validation)
   ↓
Step 2: IR → ActionDag
   ↓
Step 3: Typechecker integration
   ↓
Step 4: Solidity DAG backend (side-by-side)
   ↓
Step 5: Flip Solidity default to DAG
   ↓
Step 6: Gambit backend over DAG
   ↓
Step 6.5: (Optional) SMT/DQBF backend over DAG
   ↓
Step 7: Remove phase-based semantics
   ↓
Step 8: Optional refinements
```

Some steps (e.g. 5 and 6) are partially parallelizable once 2–4 are stable.

---

## Error Handling Strategy (applies to all steps)

To keep behaviour consistent:

* `ActionDag.from(...)` returns **`null`** on invalid graphs (cycles, visibility violations).
* The **typechecker** converts `null` into a user-facing diagnostic: “Invalid dependency structure…”.
* **Backends** (`generateSolidityFromDag`, Gambit DAG backend, etc.) assume they get a valid `ActionDag` and may use `?: error("Invalid dependency structure")` as a last resort.

This keeps user-visible errors centralized in the checker; backends are allowed to be “assertive”.

---

## Step -1 – Environment Verification

**Goal:** Ensure you can build and run tests, and know where core pieces live.

**Checklist (fill in locally):**

* [ ] Build toolchain works (`mvn test`).
* [ ] Test suite runs (even if some tests currently fail).
* [ ] You know where to find:

    * [ ] IR types (e.g. `GameIR`, signatures, phases).
    * [ ] Existing DAG infra (`vegas/dag/`).
    * [ ] Backends (Solidity, Gambit, SMT if present).
    * [ ] Example games (`*.vg`).
* [ ] You’ve scanned `DESIGN.md` for the high-level semantics you’re aiming for.

**Exit criteria**

You can run the build/tests consistently and navigate to the relevant modules without guessing.

---

## Step 0 – Verify Baseline Behaviour

**Goal:** Lock in a known-good baseline for the *current* (phase-based) system.

**Checklist:**

* [ ] Run the test suite once.
* [ ] Confirm that example games:

    * parse,
    * build IR,
    * and generate Solidity via the current backend.
* [ ] Optionally, note:

    * time to run tests,
    * rough number of tests passing.

You don’t need to change code here; just ensure you have a mental “baseline” to compare against once DAG-based code starts touching backends.

**Exit criteria**

* You know that:

    * the phase-based pipeline currently works “well enough” for examples,
    * and any regressions you see later are likely DAG integration issues.

---

## Step 1 – Introduce `ActionId` and `ActionDag` (In Isolation)

**Goal:** Create and test a specialized DAG abstraction (`ActionDag`) independent of IR/backends.

### 1.1 Define `ActionId` & `ActionMetadata`

**File:** `vegas/ir/ActionDag.kt` (new)

```kotlin
typealias ActionId = Pair<RoleId, Int> // (role, stepIndex)

data class ActionMetadata(
    val role: RoleId,
    val writes: Set<FieldRef>,            // fields written/introduced
    val visibility: Map<FieldRef, Visibility>,
    val guardReads: Set<FieldRef>         // fields read in guards/where
)

enum class Visibility { COMMIT, REVEAL, PUBLIC }
```

### 1.2 Define `ActionDag` wrapper

**File:** `vegas/ir/ActionDag.kt`

```kotlin
class ActionDag private constructor(
    private val underlying: Dag<ActionId>,
    private val meta: Map<ActionId, ActionMetadata>
) : Dag<ActionId> by underlying {

    fun metadata(a: ActionId): ActionMetadata = meta[a]!!
    fun owner(a: ActionId): RoleId = metadata(a).role
    fun writes(a: ActionId): Set<FieldRef> = metadata(a).writes
    fun visibility(a: ActionId): Map<FieldRef, Visibility> = metadata(a).visibility
    fun guardReads(a: ActionId): Set<FieldRef> = metadata(a).guardReads

    fun canExecuteConcurrently(a: ActionId, b: ActionId): Boolean =
        !Algo.reaches(a, b, ::prerequisitesOf) &&
        !Algo.reaches(b, a, ::prerequisitesOf)

    companion object {
        fun from(
            nodes: Set<ActionId>,
            prerequisitesOf: (ActionId) -> Set<ActionId>,
            metadata: (ActionId) -> ActionMetadata
        ): ActionDag? {
            val dag = ExplicitDag.from(nodes, prerequisitesOf, checkAcyclic = true)
                ?: return null
            val metaMap = nodes.associateWith(metadata)

            if (!checkCommitRevealOrdering(dag, metaMap)) return null
            if (!checkVisibilityOnReads(dag, metaMap)) return null

            return ActionDag(dag, metaMap)
        }
    }
}
```

### 1.3 Implement validation helpers

Still in `vegas/ir/ActionDag.kt`:

```kotlin
private fun checkCommitRevealOrdering(
    dag: Dag<ActionId>,
    meta: Map<ActionId, ActionMetadata>
): Boolean {
    // For each field that has both COMMIT and REVEAL:
    // - find the commit action(s)
    // - find the reveal action(s)
    // - require: every reveal has some commit that reaches it
    val commitsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()
    val revealsByField = mutableMapOf<FieldRef, MutableList<ActionId>>()

    for ((a, m) in meta) {
        m.visibility.forEach { (field, vis) ->
            when (vis) {
                Visibility.COMMIT -> commitsByField.getOrPut(field) { mutableListOf() }.add(a)
                Visibility.REVEAL -> revealsByField.getOrPut(field) { mutableListOf() }.add(a)
                Visibility.PUBLIC -> {}
            }
        }
    }

    for ((field, reveals) in revealsByField) {
        val commits = commitsByField[field].orEmpty()
        if (commits.isEmpty()) continue // no prior commit; may be allowed or rejected elsewhere
        for (r in reveals) {
            // At least one commit must reach this reveal
            val ok = commits.any { c -> Algo.reaches(c, r, dag::prerequisitesOf) }
            if (!ok) return false
        }
    }
    return true
}

private fun checkVisibilityOnReads(
    dag: Dag<ActionId>,
    meta: Map<ActionId, ActionMetadata>
): Boolean {
    // Actions may only read fields that are PUBLIC or REVEALed by some predecessor
    for ((a, m) in meta) {
        for (field in m.guardReads) {
            val ok = meta.any { (b, mb) ->
                // b is predecessor of a
                Algo.reaches(b, a, dag::prerequisitesOf) &&
                // and b makes field visible (PUBLIC or REVEAL)
                when (mb.visibility[field]) {
                    Visibility.PUBLIC, Visibility.REVEAL -> true
                    else -> false
                }
            }
            if (!ok) return false
        }
    }
    return true
}
```

You can refine the exact policy later (e.g. decide whether reading an unrevealed but public initial field is allowed), but this makes the plan executable.

### 1.4 Core tests for `ActionDag`

**File:** `src/test/kotlin/vegas/ActionDagCoreTest.kt`

Create small, synthetic DAGs (no IR yet):

* chain A → B → C,
* diamond A → B, A → C, {B,C} → D,
* intentionally cyclic graph (A → B, B → A).

Test:

* `ActionDag.from` returns non-null for acyclic cases,
* `topo()` never orders a node after its dependents,
* `canExecuteConcurrently` matches reachability,
* `from` returns null for cycle case.

**Exit criteria**

* `ActionDag` is implemented and unit-tested in isolation.
* No integration with IR or backends yet.

---

## Step 2 – Build `ActionDag` from `GameIR` (Not Yet Used by Backends)

**Goal:** Add an IR→`ActionDag` projection, exercised only by tests or a debug command.

### 2.1 Implement IR→ActionDag

**File:** `vegas/ir/ActionDag.kt`

```kotlin
fun buildActionDag(ir: GameIR): ActionDag? {
    val nodes = mutableSetOf<ActionId>()
    val deps = mutableMapOf<ActionId, MutableSet<ActionId>>()

    // 1. Create nodes
    ir.phases.forEachIndexed { step, phase ->
        phase.actions.forEach { (role, _) ->
            nodes += ActionId(role, step)
        }
    }

    // 2. Populate dependencies and metadata helpers
    fun prereqs(a: ActionId): Set<ActionId> =
        deps[a].orEmpty()

    fun buildMeta(a: ActionId): ActionMetadata {
        val (role, step) = a
        val sig = ir.phases[step].actions[role]!!

        // This logic can be as simple or precise as you want initially
        val writes = inferWritesFromSignature(role, sig)
        val visibility = inferVisibilityForWrites(role, step, ir, sig, writes)
        val guardReads = inferGuardReads(sig)

        return ActionMetadata(
            role = role,
            writes = writes,
            visibility = visibility,
            guardReads = guardReads
        )
    }

    // TODO: fill deps[...] based on:
    // - guardReads: depend on prior writers of those fields
    // - commit→reveal: reveal depends on commit
    // The exact shape can be iterated later; start conservative.

    return ActionDag.from(nodes, ::prereqs, ::buildMeta)
}
```

Use simple, obviously sound heuristics first (e.g. actions in later phases depend on all actions in earlier phases) and then refine as you better model guard-reads and commit-reveal.

### 2.2 IR→ActionDag tests

**File:** `src/test/kotlin/vegas/ActionDagFromIrTest.kt`

For each example game:

* parse → IR → `buildActionDag(ir)`:

    * assert non-null,
    * assert `dag.nodes` non-empty,
    * for a game with obvious commit/reveal structure, assert:

        * commits precede reveals in `topo()` or via `Algo.reaches`.

**Exit criteria**

* For existing example IRs, you can build an `ActionDag`.
* This still isn’t wired into the typechecker or backends.

---

## Step 3 – Integrate `ActionDag` into Typechecking

**Goal:** Make invalid dependency/visibility structures a *static error*, but keep all runtime semantics phase-based.

### 3.1 Checker hook

**File:** typechecker module (e.g. `vegas/TypeChecker.kt`)

After existing static checks:

```kotlin
val ir = ast.toIR()
val dag = buildActionDag(ir)

if (dag == null) {
    errors += StaticError(
        message = "Invalid dependency structure (cycle or visibility violation)",
        location = ast.location // or nearest relevant node
    )
}
```

### 3.2 Negative tests

**File:** `src/test/kotlin/vegas/ActionDagTypecheckTest.kt`

Create a couple of small `.vg` files that:

* read a hidden/committed field before reveal,
* explicitly create a cycle in dependencies (if you have syntax for that, or via malformed phases).

Assert:

* compilation fails with an error containing “Invalid dependency structure”.

**Exit criteria**

* For valid games, compilation behaves exactly as before.
* For intentionally invalid dependency structures, the checker rejects them.

Backends are still untouched at this step.

---

## Step 4 – DAG-Based Solidity Backend (Alongside Phase-Based Backend)

**Goal:** Generate Solidity directly from `ActionDag`, but keep phase-based backend as a reference for now.

### 4.1 Linearize `ActionDag` for action IDs

**File:** `vegas/backend/solidity/DagFromIr.kt` (new)

```kotlin
fun linearizeDag(dag: ActionDag): Map<ActionId, Int> =
    dag.nodes
        .sortedWith(compareBy({ it.second }, { it.first.name }))
        .mapIndexed { idx, id -> id to idx }
        .toMap()
```

Use these indices for:

* `uint constant ACTION_Foo_Bar = k;`
* `mapping(uint => bool) actionDone;`
* `mapping(uint => uint) actionTimestamp;` (for future timeouts).

### 4.2 Modifiers

In the Solidity DSL model:

```solidity
mapping(uint => bool) public actionDone;
mapping(uint => uint) public actionTimestamp;

modifier depends(uint actionId) {
    require(actionDone[actionId], "dependency not satisfied");
    _;
}

modifier notDone(uint actionId) {
    require(!actionDone[actionId], "already done");
    _;
}
```

### 4.3 Per-action functions

In `generateSolidityFromDag(ir, dag: ActionDag)`:

* Compute `val index = linearizeDag(dag)`.
* For each `actionId` in `dag.topo()`:

    * Collect prerequisites: `dag.prerequisitesOf(actionId)`.
    * Generate a function:

      ```solidity
      function move_Role_step(...)
          external
          by(Role)
          notDone(ACTION_Role_step)
          depends(ACTION_dep1)
          depends(ACTION_dep2)
      {
          // existing phase-based payload logic, minus phase checks
  
          actionDone[ACTION_Role_step] = true;
          actionTimestamp[ACTION_Role_step] = block.timestamp;
      }
      ```

Payload logic (commit/reveal/public, where clause checks) should be re-used from the existing backend, just without referencing `phase`.

### 4.4 API/CLI switch

Add a function:

```kotlin
fun compileToSolidity(ast: GameAst, useDag: Boolean = false): SolidityContract {
    val ir = ast.toIR()
    val dag = buildActionDag(ir) ?: error("Invalid dependency structure")
    return if (useDag) generateSolidityFromDag(ir, dag)
           else generateSolidityFromIr(ir) // existing phase-based backend
}
```

CLI example:

```bash
vegas solidity --use-dag examples/MontyHall.vg
```

(Implementation of the flag is up to your CLI layer.)

### 4.5 Tests

**File:** `src/test/kotlin/vegas/SolidityDagBackendTest.kt`

For each example:

* generate Solidity via both backends:

    * assert the DAG-based contract:

        * has no `phase` storage variable,
        * defines `ACTION_` constants,
        * uses `actionDone` and `depends`.
    * optionally, run `solc` on the output and assert success.

For one or two simple traces, you can also:

* exercise both contracts in a lightweight harness and check they accept/reject the same call sequences.

**Exit criteria**

* DAG-based Solidity generation works on examples.
* Old backend is still available for comparison.

---

## Step 5 – Make DAG-Based Solidity the Default

**Goal:** Flip the default to the DAG backend; keep the phase backend as an explicit legacy option.

### 5.1 Flip default

Change:

```kotlin
fun compileToSolidity(ast: GameAst, useLegacyPhaseBackend: Boolean = false): SolidityContract
```

and invert the boolean logic so that:

* default (`false`) uses DAG backend,
* `true` opts into legacy phase backend.

Update CLI help accordingly (`--legacy-phase-backend` instead of `--use-dag`).

### 5.2 Tests

* Keep testing the DAG backend as main path.
* Add one test that still exercises the legacy backend so it doesn’t silently break while it exists.

**Exit criteria**

* The DAG backend is the normal way of generating Solidity.
* Phase-based backend is only used intentionally.

---

## Step 6 – Gambit / EFG Backend over `ActionDag`

**Goal:** Rebuild the Gambit EFG using `ActionDag` instead of phases, to get accurate simultaneity and information sets.

### 6.1 Implement `DagGameTreeBuilder`

**File:** `vegas/backend/gambit/DagFromIr.kt` (new)

Sketch:

```kotlin
class DagGameTreeBuilder(
    private val ir: GameIR,
    private val dag: ActionDag
) {
    fun build(): GameTree {
        val frontier = FrontierMachine.from(dag) // or your existing constructor
        return buildFromFrontier(frontier, State.empty())
    }

    private fun buildFromFrontier(
        frontier: FrontierMachine<ActionId>,
        state: State
    ): GameTree {
        if (frontier.isComplete()) {
            val payoffs = evalPayoffs(ir, state)
            return GameTree.Terminal(payoffs)
        }

        val enabled = frontier.enabled() // set of ActionId
        val byRole = enabled.groupBy { dag.owner(it) }

        // pick a role to move (deterministic order)
        val (role, actions) = byRole.entries.sortedBy { it.key.name }.first()

        val knownFields = computeKnownFields(actions)
        val infosetId = infosetManager.getInfoset(role, knownFields)

        val choices = actions.flatMap { actionId ->
            val sig = ir.phases[actionId.second].actions[actionId.first]!!
            val legalPackets = enumeratePackets(sig, state, role)
                .filter { pkt -> guardHolds(sig, state, pkt) }

            legalPackets.map { pkt ->
                val newState = applyMove(state, role, pkt)
                val newFrontier = frontier.copy().apply { resolve(actionId) }
                val subtree = buildFromFrontier(newFrontier, newState)

                GameTree.Choice(
                    action = pkt,
                    subtree = subtree,
                    probability = chanceProbabilityIfNeeded(role, legalPackets.size)
                )
            }
        }

        return GameTree.Decision(role, infosetId, choices)
    }

    private fun computeKnownFields(actions: List<ActionId>): Set<FieldRef> {
        // Fields known for these actions: those written by predecessors with
        // non-COMMIT visibility.
        val result = mutableSetOf<FieldRef>()
        for (a in actions) {
            dag.prerequisitesOf(a).forEach { pred ->
                dag.writes(pred).forEach { field ->
                    val vis = dag.visibility(pred)[field]
                    if (vis == Visibility.PUBLIC || vis == Visibility.REVEAL) {
                        result += field
                    }
                }
            }
        }
        return result
    }
}
```

You can refine `State`, `Knowledge`, and information-set management as needed; the point is that knowledge comes from DAG-visible predecessors, not from phase numbers.

### 6.2 Side-by-side migration

Add:

```kotlin
fun compileToGambit(ast: GameAst, useDag: Boolean = false): EfgGame {
    val ir = ast.toIR()
    return if (useDag) {
        val dag = buildActionDag(ir) ?: error("Invalid dependency structure")
        val tree = DagGameTreeBuilder(ir, dag).build()
        tree.toEfg()
    } else {
        existingGambitBackend(ir) // phase-based
    }
}
```

### 6.3 Tests

**File:** `src/test/kotlin/vegas/GambitDagBackendTest.kt`

For at least one example:

* generate EFG via both backends,
* assert:

    * same leaf payoffs,
    * same move labels,
    * information sets are consistent, with DAG possibly giving *finer* ones (this may need manual inspection / more nuanced assertions).

Also:

* test that two actions that `ActionDag` considers concurrent (mutually non-reachable) show up as simultaneous / in the same information block where appropriate.

**Exit criteria**

* Gambit export works with DAG,
* Phase-based Gambit backend is no longer needed (can be removed in Step 7).

---

## Step 6.5 – (Optional) SMT / DQBF Backend over `ActionDag`

**Goal:** If you already have an SMT/DQBF backend, decide explicitly whether to align it with `ActionDag` now or treat it as future work.

**Two options:**

1. **If SMT backend exists and you care about it now:**

    * Introduce a DAG-aware variant, e.g.:

      ```kotlin
      fun generateDQBF(ir: GameIR, dag: ActionDag): String {
          val quantifiers = dag.topo().map { action ->
              val role = dag.owner(action)
              val vars = dag.writes(action)
              val deps = dag.prerequisitesOf(action).flatMap { dag.writes(it) }
 
              // map role → ∃ or ∀, vars+deps to DQBF syntax
              ...
          }
          ...
      }
      ```

    * Add a `useDag` flag analogous to Gambit/Solidity.

2. **If SMT backend is incomplete or low-priority:**

    * Explicitly mark it as **future work** in docs and ignore it during Steps 0–7.
    * Optionally add a note in `DESIGN.md`: “SMT/DQBF backend will be updated to use `ActionDag` after core Solidity + Gambit migration.”

**Exit criteria**

* You’ve made an explicit decision for SMT:

    * either migrated it to use DAG,
    * or consciously deferred it.

---

## Step 7 – Remove Phase-Based Scheduling Semantics

**Goal:** Once Solidity and Gambit are DAG-based, remove the old phase-barrier semantics.

**What to remove**

* `phase` variables and `nextPhase` functions in Solidity backend.
* Phase-based Gambit backend and any code that treats phase number as a semantic barrier.
* Any “phase” references that exist purely for ordering/synchronisation (you can keep phase indices as neutral IR step indices if helpful for debugging).

**What to keep**

* `ActionId`’s integer component as “step index” or “IR position” if convenient.
* Any phase information that is *purely syntactic* or helpful for error messages, as long as the semantics are entirely DAG-driven.

**Tests**

* Remove tests that assert “phase must be X” semantics.
* Assert that:

    * all contract preconditions are expressed via `depends` / `actionDone`,
    * EFG generation uses `ActionDag`, never phase numbers, for simultaneity / info sets.

**Exit criteria**

* The only semantic story is the `ActionDag` and its metadata.
* Phases, if present at all, are implementation details of the IR, not part of the semantics.

---

## Step 8 – Optional Refinements

After Steps 1–7 are stable:

* Improve error messages for DAG failures:

    * explicit cycle path,
    * name of the field causing a visibility violation.
* Enrich `ActionMetadata` with explicit property bundles derived from `where` clauses.
* Add more thorough backend equivalence tests:

    * property-based tests generating random strategies and comparing resulting payoffs,
    * stricter comparisons of EFG structures.


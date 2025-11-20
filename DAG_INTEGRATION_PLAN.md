## Doc 1 (revised) — ADR-DAG-001: Execution DAG, Visibility & Witness/Property Semantics

**Related Documents:**
- `DESIGN.md` - Detailed implementation specification, testing strategy, and backend integration details
- This document (DAG_INTEGRATION_PLAN.md) - Core architectural decisions and semantic model

### 1. Core semantic model

We keep the earlier decision:

* Nodes = **actions**.
* Edges = **must-happen-before** dependencies.
* Per-field **visibility** = `COMMIT | REVEAL | PUBLIC`.

But we now *explicitly* think of each node as carrying a **witness + properties** pair:

* `w` — a tuple of *witness values* (some hidden, some public).
* `P` — a set of *public properties* (predicates) over:

    * current and past witnesses,
    * any other global state.

Concretely in Vegas today:

* Witnesses are the **parameters** of the action (`Signature.parameters`), some of which are `hidden`.
* Public properties are the **`where` clause** and any other semantic constraints we decide to treat as “announced facts”.

So semantically an action is:

```text
Action node A:
  witnesses  : w_A   (values chosen/controlled at this node)
  properties : P_A   (boolean formulas, publicly asserted)

Execution:
  - w_A may be partially hidden or public (COMMIT / REVEAL / PUBLIC).
  - P_A becomes common knowledge once A has occurred.
```

This gives us two “channels” per node:

1. **Witness channel:** actual values (maybe private, maybe public).
2. **Property channel:** public boolean information about those values.

The DAG is about *witness flow*: who must happen before whom, so that properties and guards make sense. The visibility annotations say which witnesses become visible at which node. The property channel is “logically public” and doesn’t need its own graph structure.

### 2. Commitment schemes as concrete patterns

Two canonical patterns you wrote down:

1. **Simple equality commit–reveal**

    * Commit node:

      ```text
      Node C:
        witness: x (hidden)
        properties: { true }
        visibility(x) = COMMIT
      ```

    * Reveal node:

      ```text
      Node R:
        witness: y (public)
        properties: { y = x }
        visibility(x) = COMMIT (still hidden storage)
        visibility(y) = REVEAL (public)
      ```

   Implementation choices:

    * *Deferred check*: store `x` hidden, on `R` check `y == x`.
    * *Crypto*: store `hash(x, nonce)` at `C`, then at `R` check `hash(y, nonce) == stored_hash`.

   Same semantics in our model: `P_R` includes the equality property; how you enforce it (plain check vs crypto) is orthogonal.

2. **Existential/image style**

    * Commit node:

      ```text
      Node C:
        witness: x (hidden)
        properties: { ∃y. image(x, y) }
        visibility(x) = COMMIT
      ```

    * Reveal node:

      ```text
      Node R:
        witness: y (public)
        properties: { image(x, y) }
        visibility(y) = REVEAL
      ```

   Again:

    * *Deferred check*: at `R` you check `image(x, y)` directly.
    * *Crypto*: `C` proves `∃y. image(x, y)` in ZK; `R` may later reveal a particular witness `y` or never reveal it.

Our design needs to *allow* these patterns; it doesn’t need to know which enforcement mechanism you picked.

### 3. What we commit to structurally

We **bake in** three things:

1. **Node abstraction**: every action node is conceptually `(w, P)` even if the implementation only partially exposes that.
2. **Visibility model**:

    * Witnesses can be hidden or public; we track this as `Visibility` per field.
    * Properties `P` are **always public** (for now: all players see the same `P`).
3. **DAG role**:

    * Enforce “you can’t talk about a witness before some node created it”.
    * Enforce “you can’t use a *public* property of a witness before the node that announced that property”.

No extra graph for properties. Knowledge about properties is purely “after the node executes, P holds and everyone knows it”.

---

## Doc 2 (revised) — SPEC-DAG-001: DependencyDag & Metadata with Witness/Property View

We keep the shape of `DependencyDag`, but we tweak the *interpretation* of metadata to match the witness/property picture.

### 1. ActionMetadata

We extend the commentary around it, and (optionally) add an explicit “witness vs property” split if you want.

Minimum change (no extra runtime overhead):

```kotlin
data class ActionMetadata(
    val role: RoleId,

    // Witness fields: action's parameters (values chosen here).
    // Some will be hidden (COMMIT), some public (REVEAL/PUBLIC).
    val writes: Set<FieldRef>,

    // Visibility of each witness at this node.
    val visibility: Map<FieldRef, Visibility>,

    // Fields that the *guard* (where clause) may read as witnesses.
    val guardReads: Set<FieldRef>

    // (Future) publicProperties: we can add a field here if/when we want
    // to track public facts explicitly; for now, they are derived from the
    // where-clause AST.
)

enum class Visibility {
    COMMIT,  // witness exists, stored hidden
    REVEAL,  // witness existing from commit is now made public
    PUBLIC   // witness is public from its first occurrence
}
```

In comments / docs, we explain:

* `writes` = witnesses introduced or updated at this node.
* `visibility(f)` = how that witness is exposed at this node.
* The **public properties** of the node are the boolean formulas in `sig.requires.condition` plus any other domain invariants you encode.

If you *want* to make properties first-class, you can add:

```kotlin
data class Prop(
    val expr: Exp,            // boolean expression (where clause fragment)
    val dependsOn: Set<FieldRef> // fields it semantically depends on (optional)
)

data class ActionMetadata(
    ...
    val properties: List<Prop> = emptyList()
)
```

For now, `properties` can just be `listOf(Prop(sig.requires.condition, getReferencedFields(sig.requires.condition)))` if you want the hook, but DAG validity logic doesn’t need to inspect the actual formulas.

### 2. DAG invariants in witness/property terms

`isValidVisibilityStructure` is exactly your “no illegal talk about hidden stuff” rule:

* For each field `f`:

    * All `REVEAL`/`PUBLIC` writes of `f` must be causally *after* any `COMMIT` writes of `f` (if they exist).
* For each `guardReads` entry:

    * If a property or guard reads `f`, then some `REVEAL`/`PUBLIC` write of `f` must be a predecessor of this node (unless `f` is a “public from birth” field).

This is precisely: you can only use public facts about a witness once some node has made them public (either by revealing the witness itself or announcing a property about it). Commit-only nodes don’t yet give you public facts; they only bind the witness.

Crypto vs plain checks doesn’t change this graph.

---

## Doc 3 (minor tweak) — PLAN-DAG-001: Backends With Witness/Property View

The backend plan mostly stays as before, but we clarify how they treat witnesses vs properties.

### 1. Solidity backend

* **Witnesses**:

    * Hidden witnesses: stored in hidden storage (commitments, hashes, or even cleartext in a private mapping if you don’t care about on-chain secrecy in dev).
    * Public witnesses: function parameters and/or public storage.

* **Properties**:

    * Implemented as runtime `require(...)` checks using:

        * where clauses (possibly deferred to reveal),
        * equality between committed and revealed witnesses,
        * other domain invariants.

The patterns you mentioned:

* `x: true` / `y: x = y`:

    * `x` is a hidden witness committed earlier; `y` is a public witness at reveal; equality check is encoded in the reveal function.
* `x: ∃y. image(x, y)` / `y: image(x, y)`:

    * At commit: either no on-chain check (just a promise), or an on-chain proof check.
    * At reveal: on-chain check `image(x, y)`.

Our DAG only cares that:

* Commit node produces `x` (hidden witness).
* Reveal node depends on commit and reads `x`.
* Any future guards that use `y` or `image(x, y)` depend on the reveal node.

### 2. Gambit backend

* The **witness values** become the underlying state in the game tree.
* The **public properties** become part of what is “known” at nodes:

    * At a node, a player’s information set incorporates all public witnesses and all `P` from predecessors.
* With the current all-or-nothing visibility, those properties are known to everyone at the same time.

Later, if you ever add per-player properties (ZK style), you’d extend the metadata to track “who knows which P” instead of changing the DAG structure.

### 3. SMT / DQBF backend

* Quantified variables correspond to witnesses (fields).
* Constraints encode properties (`P`) over those witnesses.
* Dependency sets in DQBF come from DAG reachability:
  a witness `f` can depend only on witnesses in its predecessors.

Again, the witness/property split is purely semantic: the solver sees variables and constraints, you know which constraints you want to treat as “properties” vs “guards”.

---

### TL;DR of the revision

* We keep the **DAG** exactly as before (actions, edges, visibility per field).

* We *rephrase* and slightly extend the design so that every action node is explicitly:

  > “choose witnesses `w`, then publicly assert properties `P(w, past)`”

* Commit–reveal patterns become just special cases of how you split witnesses and properties across nodes, not special cases in the DAG structure.

* The design now clearly leaves room for:

    * More expressive properties (`∃y. image(x, y)` etc.),
    * Crypto-based enforcement (instead of plain `require`),
    * Future ZK/MPC work, without changing the core DAG story.

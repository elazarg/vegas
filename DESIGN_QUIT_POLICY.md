# Design: Decoupling Quit Policies in Vegas

## Overview

"Quit" semantics in Vegas determine what happens when a player abandons the game (e.g., via timeout or explicit quit). Currently, this logic is scattered:
- **Surface**: `withdraw` clauses manually check `null` values.
- **Semantics**: Hardcoded `PlayTag.Quit` and `Expr.Const.Quit`.
- **Backend**: Hardcoded `bailed` maps and `depends` logic.

This design introduces a first-class `QuitPolicy` in the IR. The policy defines the "induced subgame" upon abandonment. This allows the system to support various strategies (e.g., "Nullify Variables", "Refund All", "Bot Substitution") pluggably.

## Architecture

### 1. The `QuitPolicy` Interface (IR)

Located in `src/main/kotlin/vegas/ir/Policy.kt`. This interface defines the behavior of the game under abandonment conditions.

```kotlin
interface QuitPolicy {
    // --- Semantics (LTS / Execution) ---

    /**
     * Called when a role quits (e.g. timeout).
     * Defines the transition to the "subgame".
     *
     * @param role The role that quit.
     * @return A QuitResult describing the impact (e.g. Continue with flag, or New DAG).
     */
    fun onQuit(role: RoleId, currentHistory: (FieldRef) -> Expr.Const?): QuitResult

    /**
     * Resolves a value read during expression evaluation.
     * Intercepts reads to implement behaviors like "Quitter's values are null" or "Substitute with Bot value".
     */
    fun resolveRead(value: Expr.Const?, field: FieldRef, isQuit: Boolean): Expr.Const?

    // --- Backend (Code Generation) ---

}

sealed class QuitResult {
    // The current standard behavior: Game continues, role is marked as quit.
    object MarkAndContinue : QuitResult()

    // Future: Game transitions to a completely different DAG/Phase.
    // data class TransitionToSubgame(val newDag: ActionDag) : QuitResult()
}
```

### 2. The `EvmQuitPolicy` Interface

Defined in `src/main/kotlin/vegas/backend/evm/Policy.kt`. This interface extends `QuitPolicy` to provide EVM-specific generation logic.

```kotlin
interface EvmQuitPolicy : QuitPolicy {
    fun storage(): List<EvmStorageSlot>
    fun helpers(): List<EvmFunction>

    // Logic injection hooks
    fun preActionLogic(role: RoleId, actionId: ActionId, dependencies: List<ActionId>): List<EvmStmt>
    fun postActionLogic(role: RoleId, actionId: ActionId): List<EvmStmt>
}
```

### 3. `StandardQuitPolicy` (Implementation)

Implements the current "Timeout -> Nullify" behavior.

- **Semantics**:
  - `onQuit`: Returns `MarkAndContinue`.
  - `resolveRead`: If role quit, returns `Expr.Const.Quit` (which translates to `null` in surface/backend).
- **Backend**:
  - `storage`: `bailed` mapping, `TIMEOUT`.
  - `checkDependency`: `if (!bailed[role]) require(actionDone...)`.

### 4. Integration

- **GameIR**: Holds `val policy: QuitPolicy`.
- **GameSemantics**: Calls `policy.onQuit` when processing a quit move. Uses `policy.resolveRead` when evaluating guards/payoffs.
- **GameToEvmIR**: Casts `ir.policy` to `EvmQuitPolicy` to generate infrastructure.

## Directory Structure

- `vegas/ir/Policy.kt` (IR Interface)
- `vegas/backend/evm/Policy.kt` (Backend Interface)
- `vegas/policy/StandardQuitPolicy.kt` (Implementation)

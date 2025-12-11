# Vegas Lightning Backend: Runtime Implementation Guide

This directory contains the **Compiler** and **Protocol Definition** for the Vegas Lightning backend.

The **Runtime** (the component that actually connects to a Lightning Node and plays the game) is currently **unimplemented**. This document specifies how to build it.

## 1. Architecture

The system follows a **Verification-First** architecture:

1.  **Compile Time:** Both players independently run `LightningCompiler.compile(gameIR, ...)` to generate a `LightningProtocol`.
    * *Result:* A finite state machine where every state has a pre-calculated, verified `abortBalance`.
2.  **Runtime:** The players connect, verifying they have the exact same `LightningProtocol`, and then execute it.

## 2. The Artifact: `LightningProtocol`

The Compiler outputs a `LightningProtocol` object. The Runtime implementer must treat this object as the "Law".

* **`states: Map<Int, ProtocolState>`**: The graph of all valid game states.
* **`ProtocolState.abortBalance`**: The **Critical Invariant**. This is the specific channel distribution (Satoshis for A, Satoshis for B) that *must* be committed to the blockchain *before* the game effectively enters this state.

## 3. Implementation Requirements

To build the Runtime, you must implement three components:

### A. The Lightning Driver (`LightningChannelDriver`)
You need an adapter for a specific Lightning implementation (e.g., LND via gRPC or Core Lightning via REST).

**Required Interface:**
```kotlin
interface LightningChannelDriver {
    /**
     * Executes a synchronized Two-Phase Commit.
     * 1. Propose new state [balanceA, balanceB] to peer.
     * 2. Wait for peer's signature.
     * 3. Send our signature.
     * 4. Revoke previous state.
     *
     * MUST BLOCK until the update is finalized or failed.
     * Returns true if successful, false if peer disconnected/refused.
     */
    fun updateState(balanceA: Long, balanceB: Long): Boolean

    /**
     * Force-closes the channel with the latest committed state.
     */
    fun forceClose()
}
````

### B. The Wire Protocol

You need a transport layer (TCP, WebSocket, or LN Custom Messages) to exchange:

1.  **Handshake:** Verification hashes of the `LightningProtocol` to ensure both players are running the same game.
2.  **Game Moves:** Serialized `Label` objects (e.g., JSON or Protobuf) indicating which transition was taken.

### C. The Execution Loop (The "Runner")

This is the core logic that was removed from `LightningRunner.kt`. The implementer must recreate this state machine.

**Invariant:** Never update the local `currentStateId` until `driver.updateState()` returns true.

#### Logic Flow:

```text
LOOP:
  Current State S = protocol.states[currentStateId]

  IF S.activePlayer is NULL:
     GAME OVER.
     The channel balance is already correct (final payout or forced abort).
     Exit.

  IF S.activePlayer == ME:
     1. Select transition T (via UI or Bot logic).
     2. Next State S_next = protocol.states[T.nextStateId]
     3. CALL driver.updateState(S_next.abortBalance)
        - If fails: Force Close & Exit.
     4. SEND T.label to peer.
     5. currentStateId = S_next.id

  IF S.activePlayer == OPPONENT:
     1. WAIT for message L from peer.
     2. Find transition T where T.label == L.
     3. Next State S_next = protocol.states[T.nextStateId]
     4. CALL driver.updateState(S_next.abortBalance)
        - Note: Peer initiated this, so driver just validates & signs.
        - If fails: Force Close & Exit.
     5. currentStateId = S_next.id
```

## 4. Bootstrapping (The "Handshake")

Before the execution loop begins, the runtime must perform a setup phase:

1.  **Exchange Game Definition:** Ensure both parties are compiling the exact same `GameIR` with the same `RoleId` mapping.
2.  **Verify Protocol:** Compare the hash of the generated `LightningProtocol` (states, transitions, balances).
3.  **Fund Channel:** Open a channel with capacity = `totalPot`.
4.  **Initial Commit:**
      * The `rootStateId` has an `abortBalance`.
      * **Crucial:** Run `driver.updateState(root.abortBalance)` *before* the game technically starts.
      * This ensures that if the game aborts at T=0, the funds are correctly allocated (e.g., returned to depositors).

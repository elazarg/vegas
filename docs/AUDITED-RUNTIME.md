# Audited runtime and watcher

**Status:** prototype, checked end to end on a local chain (`EthWatcherTest`).
**Scope:** how Vegas realizes the service contract of [SE_RUNTIME_SPEC.md](../SE_RUNTIME_SPEC.md)
on an EVM chain, what the contract and the watcher enforce, and what is assumed.

## Why a watcher at all

A generated contract enforces who may move, when, and with which values. It
cannot see what players *broadcast*. On a public chain every transaction is
readable while it is pending, and a transaction that reverts still publishes
its calldata. A player can therefore disclose a hidden choice before the
game allows it, by sending a transaction the contract will reject, or one that
never gets included at all. The opponent reads it and reacts.

`examples/Coordination.vg` shows why this matters for equilibrium. Both
players choose simultaneously and both want to meet; Alice prefers the opera,
Bob the fight. If Alice broadcasts her opening before Bob chooses, Bob follows
her and Alice turns her worst equilibrium (4) into her best outcome (16). The
source game has no such move. VegasCore's sequential-equilibrium theorem
(`Vegas.Paper.source_audited_raw_sequential_equilibrium`) preserves every
source equilibrium only when departures like this are deterred by a sound,
covered, terminal audit with a fixed deposit.

## What the audited contract does

Compile with an audit policy (`compileToEvm(game, AuditPolicy(...))`, or
`--audited` on the command line). Solidity only; the Vyper backend refuses
an audit policy rather than emitting an unaudited contract.

1. **Bond.** Every strategic role joins with its stake plus a bond
   `ceil(range / coverage)`. The range used is the whole pot, since every payout
   lies between zero and the pot. This is VegasCore's `rosterAuditDeposit` with
   a conservative range bound; `coverage` is the collection-probability lower
   bound the deployment claims for its watcher.
2. **Authenticated phase.** Every move carries `ctx`, the hash of the block in
   which its node became ready. Nobody knows a block hash before the block is
   sealed, so a signed move proves it was created after its node was ready. An
   early move necessarily carries a wrong context, and stays wrong forever: it
   cannot later be included as a legal move. No trusted clock or observer
   timestamp is needed. If the hash ages out of `blockhash` (256 blocks), the
   next settlement re-anchors the node at a fresh, still unknown block.
3. **Registry of permitted traffic.** The contract records the calldata hash of
   every call an account makes successfully. Under the protected-service
   assumption below, an honest client's calls always succeed.
4. **Terminal audit.** Once play has ended (every node resolved, or the
   instance aborted), an audit window opens. Anyone may submit a transaction
   signed by a game account, as the exact signed payload plus signature.
   The contract recovers the signer itself. The record is forbidden unless
   it is a call to this contract whose calldata was executed successfully.
   Re-sending an executed call is an alias and carries no new information.
   A forbidden record burns the signer's bond, once per role.
5. **Settlement.** After the window, each role withdraws its payout plus its
   bond, unless the bond was burned. Nothing is reported during play: evidence
   is only accepted after play ends, so the audit adds no observation to the
   game.

The rule "forbidden = not a successful call to this contract" covers
disclosure through reverted calls, never-included (pending or queued)
transactions, replaced transactions with different calldata, and transactions
to any other address. It needs no inspection of hidden commitment values and
charges no legal source behaviour, including quitting: silence is never
evidence.

## What the watcher does

`vegas.watcher.Watcher` reads the game accounts from the contract and keeps
every transaction they sign that it sees: in blocks (included, successful or
reverted) and in the pools (`txpool_content`: pending and queued) of every node
it is given. A transaction that reaches only some nodes is caught only if one
of them is watched, so a deployment should watch several, well-connected
nodes. After play ends the watcher asks the contract to classify each record
(`eth_call` of `report`) and submits the chargeable ones; `vegas watch` runs
it. The watcher is trusted only for **coverage**:

- It cannot frame a player: the contract recovers the signer, and an honest
  player's only signatures are successful calls.
- It cannot backdate or forge a phase: the phase is inside the signed payload.
- It can fail to collect. That is the coverage assumption, and it is not
  established by a test.

All five transaction types are encoded: legacy (with or without EIP-155),
access-list (1), dynamic-fee (2), blob (3) and set-code (4). The encoding is
checked exactly: the rebuilt signed envelope hashes to the node's transaction
hash. A transaction of an unknown future type is listed in
`Watcher.unsupported` rather than dropped.

## Assumptions, as the spec asks

| Obligation (SE_RUNTIME_SPEC.md) | How this runtime meets it | What remains assumed |
| --- | --- | --- |
| Bounded, protected execution | Readiness-relative deadlines per node; a move after its deadline is rejected; each node resolves once. | Protected inclusion: an honest move sent in time is included in time. Censorship or congestion past a deadline turns an honest move into a reverted call, which is charged. Clients must keep a margin before deadlines. The number of messages is bounded only economically: every extra message is chargeable. |
| Raw player behaviour | Classification covers arbitrary transactions from game accounts, not the scripted client. | Accounts are fresh and dedicated to one game until settlement. |
| Authentic evidence | Signed payloads; phase bound by the readiness block hash. | Final inclusion: a reorganization of a readiness block would invalidate honest contexts. Clients should wait for finality. |
| Sound conformance checks | Permitted = successful call; no hidden values inspected; quitting is never charged. | None beyond the above. |
| Uniform partial coverage | The chain is complete for included traffic; the watcher polls the pool for the rest. | The claimed `coverage` for traffic that is never included must hold for every route and timing a deviator can choose. Traffic handed to the opponent off-chain (a direct message, a private relay) is outside the covered medium: closed communication is assumed. |
| Terminal audit and settlement | Evidence only after play; fixed bond from the pot; burn on a first charge. | Utilities are quasi-linear in the paid amounts; bonds are collectible because they are escrowed at join. Capital cost of the bond is not modelled. |

Public chance (`sample`) uses a beacon fixed at deployment
(`EntropySource.Beacon`): the draw uses the first round after the node becomes
ready, so nobody chooses its time or outcome. The beacon must be
unpredictable, unbiased and live. `contracts/VrfBeacon.sol` adapts Chainlink
VRF v2.5: anyone may request the round for a readiness time once it has
passed, each is requested and fulfilled once, and only the coordinator can
fulfil it. It is tested against a stand-in coordinator with the same
interface, not against Chainlink's deployed contracts. Block-derived randomness does not qualify:
before this runtime, anyone could trigger a draw through a contract that
reverted unless the outcome suited them.

## Tests

- `EthWatcherTest`: honest play is never charged; an opening disclosed early
  is caught whether it stays queued in the pool or is included and reverted,
  also in blob and set-code transactions, and the burned bond exceeds the
  deviation's gain; replays of executed calls and outsiders' transactions are
  not evidence; a signed early move cannot be replayed once the node is
  ready; a leak that reaches only another node is caught only if that node's
  pool is watched.
- `EthTransactionTypesTest`: the watcher rebuilds all five transaction types
  exactly.
- `EthVrfBeaconTest`: a draw served by the VRF adapter.
- `EthAdversarialTest`: timeouts blame only nodes that were ready, quitters
  keep their payouts, missing joins abort with refunds, and draws cannot be
  chosen.
- `EthModelTest`: model traces, including quits (as silence past a deadline)
  and draws (through a test beacon), give the model's payoffs on chain.

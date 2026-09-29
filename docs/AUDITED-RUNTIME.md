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
   `ceil(range / coverage)`, where `range` is the role's payout range over
   every way the game can end: every terminal history of the model, including
   quits and all chance outcomes, and an aborted instance (refund). A game too
   large to enumerate falls back to the whole pot, which bounds every payout.
   This is VegasCore's `rosterAuditDeposit`; `coverage` is the
   collection-probability lower bound the deployment claims for its watcher.
2. **Grants in a fixed order.** Events are granted one at a time, in schedule
   order: each waits for the event before it, as in VegasCore's roster
   service, so concurrent commitments are not left to land in whatever order
   the network chooses. Joins precede play and stay concurrent.
3. **Authenticated phase.** Every move carries `ctx`, the hash of the block in
   which its node became ready. Nobody knows a block hash before the block is
   sealed, so a signed move proves it was created after its node was granted.
   An early move necessarily carries a wrong context, and stays wrong forever:
   it cannot later be included as a legal move. No trusted clock or observer
   timestamp is needed. If the hash ages out of `blockhash` (256 blocks), the
   next settlement re-anchors the node at a fresh, still unknown block.
4. **Missed bindings.** A role that lets one of its own commitments expire
   loses its bond. The theorem is about the source game in which every
   commitment binds a value; a player who wants the effect of quitting commits
   and then withholds the opening, which is never charged. Silence at a public
   move or at an opening is withholding, and costs nothing beyond the game's
   own payoffs. A role that has already quit is not charged again for the
   nodes its quit resolves.
5. **Terminal audit.** Once play has ended (every node resolved, or the
   instance aborted), an audit window opens. Anyone may submit a transaction
   signed by a game account, as the exact signed payload plus signature. The
   contract recovers the signer itself and judges the record by its content
   in the phase it names (`isPermitted`). A game account's permitted
   transactions are plain calls to this contract (legacy, or type 1 or 2 with
   an empty access list) that carry exactly the ETH the call requires and
   canonical calldata, and are one of:
   - a move of a node its role owns, whose context is that node's readiness
     hash, and whose content passes the move's checks: the domain, the guard,
     and, for an opening, the commitment;
   - `settle()`, or its own role's withdrawal.

   Everything else burns the signer's bond, once per role: an opening sent
   before its node was granted, an opening that does not open the commitment
   or fails its guard, a move of someone else's node, any call with data
   appended, a transaction to another address, and any blob or set-code
   transaction, whose blobs and authorizations could carry a secret whatever
   the call. Whether a permitted move was included, was late, or reverted
   does not matter, so replays, fee bumps and moves that miss their deadline
   are never charged. The check needs no hidden commitment value. Reporting
   is left to accounts outside the game: a game account's `report` call would
   carry arbitrary data.
6. **Settlement.** After the window, each role withdraws its payout plus its
   bond, unless the bond was burned. Nothing is reported during play: evidence
   is only accepted after play ends, so the audit adds no observation to the
   game. (A missed binding is charged when it happens, but it is public
   already.)

## What the watcher does

`vegas.watcher.Watcher` reads the game accounts from the contract and keeps
every transaction they sign that it sees: in blocks (included, successful or
reverted) and in the pools (`txpool_content`: pending and queued) of every node
it is given. A transaction that reaches only some nodes is caught only if one
of them is watched, so a deployment should watch several, well-connected
nodes. After play ends the watcher asks the contract to classify each record
(`eth_call` of `report`) and submits the chargeable ones; `vegas watch` runs
it. The watcher is trusted only for **coverage**:

- It cannot frame a player: the contract recovers the signer and classifies
  the record itself, and an honest player signs only permitted content.
- It cannot backdate or forge a phase: the phase is inside the signed payload.
- It can fail to collect. That is the coverage assumption, and it is not
  established by a test.

Evidence is transferable: whoever holds a signed transaction can report it,
including the opponent a leak was sent to. Reporting costs gas and earns
nothing, because a burned bond goes to no one; paying the reporter from the
bond would give players a stake in each other's violations, which the
theorem's burned deposit excludes. The audit is a service whose operator is
paid, or motivated, outside the game.

All five transaction types are decoded: legacy (with or without EIP-155),
access-list (1), dynamic-fee (2), blob (3) and set-code (4). The encoding is
checked exactly: the rebuilt signed envelope hashes to the node's transaction
hash. A transaction of an unknown future type is listed in
`Watcher.unsupported` rather than dropped.

## Assumptions, as the spec asks

| Obligation (SE_RUNTIME_SPEC.md) | How this runtime meets it | What remains assumed |
| --- | --- | --- |
| Bounded, protected execution | Events granted one at a time; readiness-relative deadlines per node; a move after its deadline is rejected; each node resolves once. | Protected inclusion: an honest move sent in time is included in time. A censored or delayed opening is not charged, but it still fails, and a censored commitment is charged as a missed binding. No ledger rules out censorship bought by an opponent; deadlines must be long enough to make it costly. Clients must keep a margin before deadlines. |
| Raw player behaviour | Classification covers arbitrary transactions from game accounts, not the scripted client. | Accounts are fresh and dedicated to one game until settlement. |
| Authentic evidence | Signed payloads; phase bound by the readiness block hash. | Final inclusion: a reorganization of a readiness block would invalidate honest contexts. Clients should wait for finality. |
| Sound conformance checks | Permitted content in the named phase; no hidden values inspected; withholding is never charged. | Fee fields (gas price and limit) are chosen freely by every sender, so they remain a covert channel of a few bytes per transaction that no content rule can close. |
| Uniform partial coverage | The chain is complete for included traffic; the watcher polls the pools for the rest. | The claimed `coverage` for traffic that is never included must hold for every route and timing a deviator can choose. A transaction handed to the opponent directly or through a private relay or builder is outside the watched medium: closed communication is assumed. |
| Terminal audit and settlement | Evidence only after play; fixed bond from the role's payout range; burn on a first charge. | Utilities are quasi-linear in the paid amounts; bonds are collectible because they are escrowed at join. The capital cost of a bond (up to the pot divided by the coverage) is not modelled, and neither is the reporter's gas. |

Public chance (`sample`) uses a beacon fixed at deployment
(`EntropySource.Beacon`). A draw uses the first round after its readiness
plus `BEACON_DELAY` (15 minutes), so that the block that made it ready is
final before the round is published: a proposer who could still include or
drop that block after seeing the round would choose the outcome. Nobody
chooses its time or outcome. The beacon must be unpredictable, unbiased and
live, and nobody may see a round before it is published. A threshold beacon
(drand) meets this under its threshold assumption. `contracts/VrfBeacon.sol`
adapts Chainlink VRF v2.5: anyone may request a round once its time has
passed, each is requested and fulfilled once, and only the coordinator can
fulfil it. A VRF operator computes the output before publishing it, so it can
bias a draw by withholding an unwelcome output; the adapter trusts it not to.
It is tested against a stand-in coordinator with the same interface, not
against Chainlink's deployed contracts. Block-derived randomness does not
qualify: whoever triggers a block-derived draw can do so from a contract that
reverts unless the outcome suits them.

## Tests

- `EthWatcherTest`: honest play is never charged; an opening disclosed early
  is caught whether it stays queued in the pool or is included and reverted;
  blob and set-code transactions are evidence whatever they call; a wrong
  opening, and a permitted call with bytes appended, are evidence; an opening
  made in its phase is not, even when it lands after its deadline; the burned
  bond exceeds the deviation's gain; replays of permitted calls and outsiders'
  transactions are not evidence; letting one's own commitment expire burns the
  bond and withholding an opening does not; events are granted one at a time;
  a signed early move cannot be replayed once the node is ready; a leak that
  reaches only another node is caught only if that node's pool is watched.
- `EthTransactionTypesTest`: the watcher rebuilds all five transaction types
  exactly.
- `EthVrfBeaconTest`: a draw served by the VRF adapter, for the round after
  the beacon delay.
- `EthAdversarialTest`: timeouts blame only nodes that were ready, quitters
  keep their payouts, missing joins abort with refunds, and draws cannot be
  chosen.
- `EthModelTest`: model traces, including quits (as silence past a deadline)
  and draws (through a test beacon), give the model's payoffs on chain.

# Audited runtime and watcher

**Status:** prototype, checked end to end on a local chain (`EthWatcherTest`).
**Scope:** how Vegas realizes the runtime of [SE_RUNTIME_SPEC.md](../SE_RUNTIME_SPEC.md)
on an EVM chain, what the contract and the watcher enforce, and what is assumed.
The VegasCore paper calls quitting *default*; this document keeps Vegas's word.

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
(`Vegas.Paper.intended_raw_sequentialEquilibrium_preserved`) preserves every
equilibrium of the intended game only when departures like this are deterred
by a covered count audit with a funded deposit.

## What the game must declare

An audited build checks the theorem's hypotheses on the game and refuses a
game that fails them:

- **Finite.** Its histories can be enumerated: every parameter has a finite
  type.
- **An exit payout.** Every role that can quit declares one, in an `exit`
  clause after the `withdraw` outcome:

  ```
  withdraw (...) ? { Alice -> 16; Bob -> 4 } : ...
  exit { Alice -> 0; Bob -> 0 }
  ```

  Once a role quits, it is paid its exit payout and nothing else; the
  outcome still decides what the other roles get. This is the paper's exit
  transfer, and it gives the theorem its fixed exit utility `a`: the role's
  utility after quitting must be one value (a `utility` clause that reads a
  private draw can break this), and no better than its utility at any
  outcome where nobody quits.

## What the audited contract does

Compile with an audit policy (`compileToEvm(game, AuditPolicy(...))`, or
`--audited` on the command line). Solidity only; the Vyper backend refuses
an audit policy rather than emitting an unaudited contract.

1. **Audit deposit.** Every strategic role joins with its stake plus an audit
   deposit `ceil(spread / coverage)`, where
   `spread = max(0, a, hi) - min(0, a, lo)` over the role's utility: `lo` and
   `hi` bound it at every terminal history of the model, including quits and
   all chance outcomes, and the 0 covers an aborted instance (every role gets
   its stake back). `coverage` is the probability `p = alpha * beta` the
   deployment claims for observing a forbidden transaction and delivering its
   report. This is the theorem's funding condition (`ClientSpec.funded`).
2. **Source order.** Events become ready one at a time, in schedule order:
   each waits for the event before it, as on VegasCore's information graph,
   so concurrent commitments are not left to land in whatever order the
   network chooses. Joins precede play and stay concurrent.
3. **Readiness credential.** Every move carries `credential`, the hash of the
   block in which its node became ready. Nobody knows a block hash before the
   block is sealed, so a signed move proves it was created after its node
   became ready. An early move necessarily carries a wrong credential, and
   stays wrong forever: it cannot later be included as a legal move. No
   trusted clock or observer timestamp is needed. If the hash ages out of
   `blockhash` (256 blocks), the next settlement re-anchors the node at a
   fresh, still unknown block.
4. **Quitting is never charged.** A role that lets one of its nodes expire,
   commitment or opening, quits: it has no further moves and is paid its
   exit payout. It owes nothing to the audit.
5. **Count audit.** Once play has ended (every node resolved, or the instance
   aborted), an audit window opens. A game account may send one well-formed
   move per node its role owns, and nothing else. Anyone may submit evidence
   that it did more, as exact signed payloads with their signatures; the
   contract recovers the signer itself.
   - `report(tx, signature)` burns the signer's deposit unless `tx` is a
     well-formed move (`isWellFormed`): a plain call to this contract (legacy,
     or type 1 or 2 with an empty access list) of the move of a node the
     signer's role owns, carrying that node's readiness credential, exactly
     the ETH the move requires and canonical calldata, with values in their
     types' domains and, for an opening, opening the role's commitment. So an
     opening sent before its node was ready, an opening that does not open
     the commitment, a move of someone else's node, a call with data
     appended, a call of `settle()` or of a withdrawal, a transaction to
     another address, and any blob or set-code transaction (whose blobs and
     authorizations could carry a secret whatever the call) are evidence.
   - `reportPair(first, firstSignature, second, secondSignature)` burns the
     signer's deposit when two transactions it signed both call the move of
     one node and are not the same transaction up to their fees: their nonce,
     value or calldata differ. A replay with a new nonce is a second
     transaction; a fee bump is not.

   Whether a move was included, was late, or reverted does not matter, so a
   verdict is fixed when the transaction is signed. A value that fails the
   move's `where` constraint is well formed: the move fails, as a failed
   publication does in the source game, and its owner quits. The check needs
   no hidden commitment value. Reporting is left to accounts outside the
   game.
6. **Settlement.** After the window, each role withdraws its payout plus its
   audit deposit, unless the deposit was burned. Nothing is reported during
   play: evidence is only accepted after play ends, so the audit adds no
   observation to the game.

The contract differs from VegasCore's count rule in one place. The count
rule accepts an opening of a commitment the sender signed even if that
commitment was never accepted. The contract checks an opening against the
commitment it accepted, so it is stricter, but only for a role that has
already quit at its commitment.

## What the watcher does

`vegas.watcher.Watcher` reads the game accounts from the contract and keeps
every transaction they sign that it sees: in blocks (included, successful or
reverted) and in the pools (`txpool_content`: pending and queued) of every node
it is given. A transaction that reaches only some nodes is caught only if one
of them is watched, so a deployment should watch several, well-connected
nodes. After play ends the watcher asks the contract to classify each record,
alone and paired with each earlier record of the same account (`eth_call` of
`report` and `reportPair`), and submits the first evidence that would burn
each role's deposit; `vegas watch` runs it. Reporting one violation per role
is enough: the charge is the same (`Vegas.Paper.firstCountReports_audit`). The
watcher is trusted only for **coverage**:

- It cannot frame a player: the contract recovers the signer and classifies
  the record itself, and an honest player signs one well-formed move per
  node.
- It cannot backdate or forge a phase: the credential is inside the signed
  payload.
- It can fail to collect. That is the coverage assumption, and it is not
  established by a test.

Evidence is transferable: whoever holds a signed transaction can report it,
including the opponent a leak was sent to. Reporting costs gas and earns
nothing, because a burned deposit goes to no one; paying the reporter from the
deposit would give players a stake in each other's violations, which the
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
| Source order and timeliness | Events ready one at a time; readiness-relative deadlines per node; a move after its deadline is rejected; each node resolves once. | Protected inclusion: an honest move sent in time is included in time. A censored move is not charged, but its owner quits. No ledger rules out censorship bought by an opponent; deadlines must be long enough to make it costly. Clients must keep a margin before deadlines. |
| Readiness credentials | The readiness block hash, unknowable before the node is ready. | Final inclusion: a reorganization of a readiness block would invalidate honest credentials. Clients should wait for finality. |
| Raw behavior | Classification covers arbitrary transactions from game accounts, not the scripted client. | Accounts are fresh and dedicated to one game until settlement. |
| Count audit, authentic | One well-formed move per owned node; signer recovered on chain; no hidden values inspected; quitting never charged. | Fee fields (gas price and limit) are chosen freely by every sender, so they remain a covert channel of a few bytes per transaction that no content rule can close. |
| Coverage | The chain is complete for included traffic; the watcher polls the pools for the rest. | The claimed `coverage` for traffic that is never included must hold for every route and timing a deviator can choose, and reports must be included before the window closes. A transaction handed to the opponent directly or through a private relay or builder is outside the watched medium: closed communication is assumed. |
| Funding | Fixed deposit from the role's utility spread and exit utility; burn on a first charge. | Utilities are quasi-linear in the paid amounts; deposits are collectible because they are escrowed at join. The capital cost of a deposit is not modelled, and neither is the reporter's gas. |

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

- `AuditDepositTest`: deposits are the utility spread, including the exit
  utility, over coverage; a utility clause sizes them; an audited build
  refuses a game without exit payouts, with an exit better than an intended
  outcome, with an exit utility that is not fixed, or that cannot be
  enumerated.
- `EthWatcherTest`: honest play is never charged; an opening disclosed early
  is caught whether it stays queued in the pool or is included and reverted;
  blob and set-code transactions are evidence whatever they call; a wrong
  opening, a well-formed call with bytes appended, and a game account's call
  of `settle()` are evidence; an opening made in its phase is not, even when
  it lands after its deadline; a replay with a new nonce is a second
  transaction for its node, and a fee bump is not; the burned deposit
  exceeds the deviation's gain; outsiders' transactions are not evidence;
  quitting is never charged, at a commitment or at an opening; events
  become ready one at a time; a signed early move cannot be replayed once
  the node is ready; a leak that reaches only another node is caught only if
  that node's pool is watched.
- `ScheduleGenerationTest`: an audited move enforces its `where` constraint,
  but the audit does not judge it.
- `EthTransactionTypesTest`: the watcher rebuilds all five transaction types
  exactly.
- `EthVrfBeaconTest`: a draw served by the VRF adapter, for the round after
  the beacon delay.
- `EthAdversarialTest`: timeouts blame only nodes that were ready, quitters
  keep their payouts, missing joins abort with refunds, and draws cannot be
  chosen.
- `EthModelTest`: model traces, including quits (as silence past a deadline)
  and draws (through a test beacon), give the model's payoffs on chain.

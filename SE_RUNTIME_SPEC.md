# Audited runtime for sequential-equilibrium preservation

The runtime a Vegas deployment must provide for the sibling
[VegasCore](../VegasCore/) development's sequential-equilibrium theorem to
apply. [docs/AUDITED-RUNTIME.md](docs/AUDITED-RUNTIME.md) describes how the
EVM backend and its watcher realize it and what they leave as assumptions.

Vocabulary: the paper's *default* (a binding omission or a failed
publication, after which the player makes no further choices) is what Vegas
calls a *quit*. In Vegas, "default" means a default value instead.

## Guarantee

The target is Theorem "Preservation under fixed exit utility"
(`thm:recovery` in [the paper](../VegasCore/overleaf/sections/06-equilibrium.tex);
Lean `Vegas.Paper.intended_raw_sequentialEquilibrium_preserved` in
[Paper.lean](../VegasCore/Paper.lean)). Under the hypotheses below, every
sequential equilibrium (SE) of the **intended game** is realized by an SE of
the ledger game:

- with the intended joint law of terminal source configuration and payoff
  vector;
- with no quits and no audit charges on its paths;
- with consistent beliefs and rational continuations at every ledger
  information set, including those created by early openings and other
  traffic the source game does not have;
- playing the intended action law at every genuine first source decision,
  and holding the intended posterior wherever the ledger looks to a player
  like a point of the intended game, even off path.

The intended game is the source game in which every commitment takes a value
its guard will accept and every reveal is attempted. It is not the full
source game: an equilibrium that relies on withholding is not covered.

The result is existential: the realizing assessment is chosen
noncomputably, so there is no executable equilibrium solver, and other
ledger equilibria are not ruled out. Deviations are covered within the
finite raw interface (any packet, for any event, with values and handles
from finite sets that include every payload value); deviations outside it
are outside the guarantee.

A weaker result needs less. The Nash correspondence (`thm:nash`) needs no
coverage and no particular deposit: with an authentic audit (one that
delivers only evidence that was really sent), clients that act at their
first turn are a Nash equilibrium of the ledger game exactly when the source
profile is one of the source game.

## Hypotheses on the game

The compiler can check these, and an audited Vegas build does (see
`auditDeposits` in `backend/evm/GameToEvmIR.kt`), except where noted.

- **Source order.** The ledger runs the *information graph*: every event
  waits for the one before it, so events become ready one at a time. The
  concurrent relaxation preserves only Nash equilibria (`thm:intended`,
  items 3 and 4); SE under concurrency is open.
- **Finiteness.** The intended game, the prior and every payload type are
  finite, and the raw interface covers every binding, publication and
  initial commitment value.
- **Well-formed setup.** At every commitment the intended game reaches, some
  value is predicted to pass its guard. Not checked by Vegas.
- **Prior.** Each player's private inputs are independent of the rest given
  a public initial signal, or there are at most two players and each event
  offers its owner a single turn. Not checked by Vegas.
- **Fixed exit utility.** A player that quit has a fixed utility `a_i`
  whatever else happens, and `a_i <= u_i` at every terminal outcome of the
  intended game. In Vegas, an `exit` clause fixes the payout of a role that
  quit (the paper's *exit transfer*), and the compiler checks that the
  role's resulting utility is fixed and no better than any outcome where
  nobody quits.
- **Utility bounds.** `lo_i <= u_i <= hi_i` at every terminal source readout
  of a legal history.

## Hypotheses on the service

The deployment must provide these; no contract can establish them alone.

- **Timeliness** (`AsyncContract`, `AsyncTimely`). On every history, an
  event's owner gets a turn within its reaction bound after readiness, the
  owner's single packet for a ready event is included within its inclusion
  bound, and play eventually completes. The two bounds sum to strictly less
  than the event's deadline. Packets of other authors, and further packets
  for the same event, have no inclusion guarantee. A block-clock
  implementation must establish these bounds separately.
- **Readiness credentials.** A packet carries its event's readiness
  credential exactly when the event's predecessors had completed in the
  public record its sender saw; a sender cannot produce one earlier.
- **Raw behavior.** Players may send any packet, at any time, including
  malformed ones, and may observe pending packets of others through any leak
  rule that depends only on the player and the pool's contents.
- **Ideal capabilities.** Commitments are hiding and binding, envelopes are
  authenticated, and a player cannot resubmit another's envelope or reuse its
  handle. A cryptographic realization needs its own refinement argument
  ([ideal commitment capabilities](../VegasCore/docs/ideal-commitment-capabilities.md)).
- **The count audit.** The audit judges each signed packet by its sender's
  own earlier packets only, so a packet's verdict is fixed when it is sent. A
  packet is permitted when it names an event its sender owns, carries that
  event's readiness credential, is the sender's first packet for that event,
  and is well formed: a commitment binds a fresh handle of the sender, and an
  opening carries a value of the payload type and opens the sender's own
  binding for that event. Everything else is forbidden. A packet that would
  fail its guard is permitted; the failure is a source outcome. Quitting is
  never charged.
- **Authentic evidence.** The audit delivers only packets that were really
  sent.
- **Coverage** `p_i = alpha_i * beta_i`. Whatever the rest of the traffic,
  a forbidden packet of player `i` is observed with probability at least
  `alpha_i` and an observed one is delivered with probability at least
  `beta_i`. An average detection rate does not establish this. Three checked
  facts bound what a watcher can achieve (paper appendix "What a watcher can
  collect"): a forbidden packet the watcher never sees can be
  indistinguishable from silence; reports are delivered with probability one
  if the ledger includes them as it includes players' moves; and if reports
  can be delayed arbitrarily, no positive bound holds uniformly.
- **Funding.** Each player posts a fixed deposit `d_i >= 0` with
  `p_i * d_i >= max(0, a_i, hi_i) - min(0, a_i, lo_i)`, burned once if any
  forbidden packet of `i` is delivered. Deposits are collectible and burned,
  not paid to anyone; utilities are quasi-linear in money and net of the
  charge. The 0 terms cover a run that never finishes, whose base payoff is 0.
- **Closed communication.** Players communicate only through registered
  accounts on the audited network. A private channel (a direct message, a
  private relay or builder) defeats coverage.

## Not covered

- SE preservation when events run concurrently.
- The capital cost of deposits of order `range / p_i`, and the cost of
  reporting.
- Covert channels the model does not have, such as fee fields.
- Chain reorganizations, which can invalidate a lawful packet's credential.
- Chance: a sample needs a live beacon that nobody can predict or bias, read
  only after the draw's inputs are final.

## Pointers

- [Ledger model and settlement](../VegasCore/overleaf/sections/05-runtime.tex),
  [the theorems](../VegasCore/overleaf/sections/06-equilibrium.tex),
  [model definitions](../VegasCore/overleaf/sections/appendix-models.tex)
  (count audit, watcher facts, hypothesis table), and
  [the boundary to a blockchain](../VegasCore/overleaf/sections/08-artifacts.tex).
- [Hypotheses as Lean fields](../VegasCore/Vegas/Game/ClientSpecification.lean):
  `ClientSpec` (`lower_le`, `le_upper`, `exitBelow`, `coverage`, `funded`, ...).
- [Count verdict](../VegasCore/Vegas/Pending/ReactiveCountVerdict.lean)
  (`countPermits`), [count audit](../VegasCore/Vegas/Pending/ReactiveCountAudit.lean),
  [reporting each sender's first violation](../VegasCore/Vegas/Pending/CountReportSelection.lean),
  and [exit utility](../VegasCore/Vegas/Game/OnePacketExclusionPayoff.lean)
  (`exclusionBase`).
- [Open problems and exact scope](../VegasCore/docs/sequential-se-open-problems.md).

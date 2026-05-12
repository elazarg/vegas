# Future Work

Items deferred from the probabilistic-design branch, grouped by area.
Each item is independently shippable.

## Backends

### PRISM-games backend

A new backend that consumes `SampleSpec.dist` directly to answer
expected-utility and probability-of-winning queries. The per-node
SampleSpec metadata is already in place; the IR is ready. PRISM's
stochastic multi-player games (SMG) model maps onto Vegas's
strategic + chance node distinction cleanly, and PRISM's PCTL /
rPATL logics fit the kinds of questions Gambit answers awkwardly
(e.g. "what is Guest's expected payoff in MontyHallChance under
uniform Host?").

Estimated cost: a backend in the style of `gambit/FromIR.kt`, walking
the EventGraph and emitting PRISM's `.prism` module syntax. The
chance-vs-strategic distinction maps directly onto PRISM's `probability` /
`player` annotations.

Tracked as [GitHub issue #50](https://github.com/elazarg/vegas/issues/50)
and `TODO.txt`.

### Real entropy sources beyond `block.prevrandao`

`sample` bindings currently use `EntropySource.PrevRandao(0)` as the
single hard-coded source (`vegas/ir/IR.kt` `DEFAULT_SAMPLE_SOURCE`).
A future entropy-source taxonomy would offer per-game choice:

- `PrevRandao(futureBlocks: Int)` with `futureBlocks >= 1` to mitigate
  proposer bias (two-action lock/consume pattern).
- Chainlink VRF: request/fulfillRandomWords callback scaffolding.
- drand beacon: BLS signature verification using `bn254` precompile.
- Multi-party commit-reveal aggregation with one-honest assumption.

Surface: either a CLI flag (`--entropy=prevrandao+2`) for project-wide
selection, or per-sample `from prevrandao(+k)` clauses for per-site
choice. Replacing the single `DEFAULT_SAMPLE_SOURCE` constant with a
config-driven value is a single-line plumbing change once the surface
is decided.

### Rejection sampling for non-uniform sample distributions on EVM

`sample (x: T ~ weighted { ... })` analyses correctly in Gambit / MAID
but is rejected at EVM emission today (the modulo-into-support trick
is only correct for uniform priors). A rejection-sampling implementation
in the emitted Solidity would draw repeatedly from prevrandao and accept
according to the weight, with a bounded retry count.

## Language semantics

### Contextual `~ D` distributions

A strategic role's `~ D` annotation today is a fixed prior. The actor
may have a state-dependent strategy (e.g., "Host prefers door 1 when
Guest picks 0") that current syntax cannot express directly. Adding
`yield Host(goat: door ~ uniform { 0, 1, 2 } given Guest.d == 0)`
or similar would let users declare context-conditional analysis priors.

Gambit already conditions per-trace via `enumerateAssignmentsForAction`,
so the IR mechanism is mostly there; surface syntax and lowering need
to be designed.

### Reveal-failure slash policy

Today a `random` actor can commit `keccak256(<out-of-support value>)`
and refuse to reveal; the game stalls with funds locked. There is no
slash. A future policy could let `commit`/`reveal` declarations carry
an `or burn N` (or `or slash`) handler triggered when the reveal-time
support check fails. Distinct from the current `or split / or burn / or null`
handlers, which fire on timeout.

### Symbolic / SMT-based pot conservation check

Pass E currently piggybacks on Gambit's enumerator. Games Gambit cannot
fully enumerate (unbounded `int` parameters, very deep trees, certain
pruning artifacts) are silently accepted. An SMT-based version would
encode the role-payoff and burn expressions symbolically and check
`forall reachable assignments. sum(payoffs) + burn == sum(deposits)`,
closing the gap.

## Known-non-conservative examples

These examples currently fail Pass E and are exempted from
`ExamplesValidationTest`'s typecheck loop. Each needs to be rewritten
to be conservative (multi-winner split arithmetic, burn-on-no-winner,
etc.) or formally accepted as non-conservative with a runtime-deposit
adjustment policy:

- `Lottery.vg` (the canonical case; an attempted rewrite is the active
  TODO).
- `ClaimFraud.vg`
- `CommitteeVoting.vg`
- `GasPriceAuction.vg`
- `HiddenReserve.vg`
- `StakingSlashing.vg`
- `TwoRobotCorridor.vg`
- `VickreyAuction.vg`

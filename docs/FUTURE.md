# Future Work

Items deferred from the probabilistic-design branch, grouped by area.
Each item is independently shippable.

## Backends

### PRISM-games backend

A new backend that consumes `SampleSpec.dist` directly to answer
expected-utility and probability-of-winning queries. The per-node
SampleSpec metadata is already in place. PRISM-games CSGs are an
exact target for the finite public-state fragment of Vegas: a
set of independent public yields becomes one joint-action CSG state,
and public chance samples become probabilistic transitions.
This fits expected-utility and probability-of-winning queries that
Gambit answers awkwardly.

Plain PRISM-games CSGs do not directly encode persistent private
information across later decisions. Commit/reveal games such as
MontyHallChance therefore remain Gambit/EFG territory unless a
future backend compiles hidden chance into public belief states.

Estimated cost: a backend in the style of `gambit/FromIR.kt`, walking
the EventGraph, quotienting public frontiers into CSG transitions,
and emitting PRISM's `.prism` plus `.props` syntax.

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

### Exact-uniform sampling on EVM for non-power-of-two support sizes

The current `keccak256(...) % supportSize` introduces a modulo bias of
order `supportSize / 2^256` (e.g. `~ 3 / 2^256 ~ 2^-254` for a 3-way
ticket). This is statistically undetectable but mathematically not
identical to the analysis-time uniform distribution. Same fix (and
gas cost): a bounded rejection loop.
```solidity
uint256 entropy = uint256(keccak256(abi.encode(block.prevrandao, address(this), idx)));
uint256 threshold = type(uint256).max - type(uint256).max % N;
uint256 attempts = 0;
while (entropy >= threshold) {
    require(attempts < 8, "exhausted attempts");
    entropy = uint256(keccak256(abi.encode(entropy, attempts)));
    attempts++;
}
uint256 r = entropy % N;
```
Worth doing only if a future deployment needs strict uniformity.
Production EVM code (Chainlink VRF consumers, NFT mints, raffles) all
accept the bias.

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

- `ClaimFraud.vg`
- `CommitteeVoting.vg`
- `GasPriceAuction.vg`
- `HiddenReserve.vg`
- `StakingSlashing.vg`
- `TwoRobotCorridor.vg`
- `VickreyAuction.vg`

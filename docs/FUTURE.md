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

### Concrete randomness beacons

`sample` bindings draw from a beacon fixed at deployment
(`EntropySource.Beacon`, interface `IVegasBeacon.randomnessAfter`): the
first round published after the node becomes ready. Block-derived
randomness was removed because whoever triggers the drawing call can
choose among outcomes. `contracts/VrfBeacon.sol` adapts Chainlink VRF v2.5. Remaining: a drand
adapter (evmnet), which must verify each round's BLS signature on BN254 on
chain, and a test of the VRF adapter against Chainlink's own contracts.

Weighted distributions are exact up to the reduction bias: the beacon
output, domain-separated by contract and node, is reduced modulo the
common denominator `D` of the weights and mapped through cumulative
integer weights, with bias below `D / 2^256`. A bounded rejection loop
would remove even that bias, if a deployment needs it.

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

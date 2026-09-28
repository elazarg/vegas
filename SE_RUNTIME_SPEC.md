# Audited runtime for sequential-equilibrium preservation

## Purpose and guarantee

Implement a runtime satisfying the service contract proved in the sibling
[VegasCore repository](../VegasCore/). For a fixed game, service, audit rule and
deposit, every source sequential equilibrium (SE) has a runtime SE with the same
joint distribution of initial parameters, public result and realized net payoff.
This is ordinary SE, including consistent beliefs and optimal continuation
behavior at information sets reached with probability zero.

The guarantee is existential preservation of each source equilibrium. It does
not assert that every runtime equilibrium comes from the source, or provide an
executable equilibrium solver. The implementation must be independent of which
source equilibrium players select.

## Required service contract

- **Bounded, protected execution.** Declare finite message/value bounds and
  activation rosters, give each event owner an opportunity to act, and implement
  the specified phase, inclusion and deadline behavior. Envelopes are included
  at most once, including rejected calls. Source choices must fit the declared
  bounds. Deadlines alone do not establish a bound on interaction.
- **Raw player behavior.** Players may submit nonconforming messages and observe
  pending traffic through the declared partial observation rule. An honest
  client is insufficient enforcement: the audit and settlement must handle
  departures by arbitrary clients within the modeled interface.
- **Authentic evidence.** Record attributable messages together with their phase
  and relevant prior ledger context. Evidence may concern pending, rejected or
  never-included messages. Signatures authenticate accounts; authenticating the
  phase and ledger context is an additional service obligation.
- **Sound conformance checks.** Classify evidence against the compiled protocol's
  permitted behavior, not a selected strategy profile. Preserve legal source
  choices, including withholding. A missing audit record is not proof of
  omission; attributing a missed binding requires the protected inclusion
  guarantee. The checker must not assume it can inspect hidden commitment values.
- **Uniform partial coverage.** For each player, supply a positive lower bound
  on the probability of collecting each forbidden record, for every actual
  traffic trace containing it. Justify the bound under the player's information
  and adaptive choices of timing, recipients and retries. An average observed
  detection rate does not establish this requirement.
- **Terminal audit and enforceable settlement.** Collect a fixed deposit and
  apply the specified sanction at settlement. The formal audit introduces no
  informative reports during strategic play. Any such reporting needs its own
  analysis. The service may be an external oracle with contract settlement;
  EVM execution alone does not supply observation of pending traffic.

## Deposits and deployment assumptions

Use a certified bound on each player's entire continuation payoff range and
the audit coverage bound to size the deposit; see `rosterAuditDeposit` below.
These quantities are fixed before selecting an equilibrium. The proof uses
utility units. A monetary implementation must state how transfers affect
utility, ensure collectibility, and account for any relevant capital costs or
external stakes.

Specify the covered communication medium and trust assumptions. Public mempool
access is not coverage of private routes or outside communication. Ordinary
unmonitored channels matter alongside covert timing or formatting channels.
The service argument must also address observation outages, censorship and
evidence delivery. A prototype can test these cases and measure costs; measured
coverage alone cannot prove the uniform lower bound.

The formal runtime uses ideal commitments and authenticated evidence. Replacing
these with cryptography requires a separate security/refinement argument,
including sharing secrets and credentials. Monitoring incentives and strategic
oracle behavior also require justification if the deployment relies on them.

## Authoritative details and pointers

- [Paper](../VegasCore/overleaf/main.tex), especially
  [the SE theorem (`thm:sequential`)](../VegasCore/overleaf/sections/05-correctness.tex)
  and [implementation boundaries](../VegasCore/overleaf/sections/07-artifacts.tex).
- [Stack and assumption table](../VegasCore/docs/se-compilation-stack.md):
  mathematical scope and remaining implementation obligations.
- [End-to-end theorem](../VegasCore/Vegas/Game/SourceServiceCompilation.lean):
  `SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved`;
  [paper-facing statement](../VegasCore/Paper.lean):
  `Vegas.Paper.source_audited_raw_sequential_equilibrium`.
- [Service specification](../VegasCore/Vegas/Game/SourceServiceLocalComparison.lean),
  [execution schedule](../VegasCore/Vegas/Game/ServiceRoster.lean),
  [audit predicate](../VegasCore/Vegas/Pending/ReactiveServiceAudit.lean), and
  [deposit bound](../VegasCore/Vegas/Game/ServicePayoffBounds.lean).
- [Enforcement discussion](../VegasCore/docs/disclosure-enforcement-design.md)
  and [ideal commitment capabilities](../VegasCore/docs/ideal-commitment-capabilities.md)
  explain the design boundaries and cryptographic questions.

For implementation precedent,
[Towards Secure and Efficient Payment Channels](https://arxiv.org/abs/1811.12740)
studies incentivized watchtowers. It does not establish the pending-message
coverage required here. [Flashbots Protect](https://docs.flashbots.net/flashbots-protect/overview)
illustrates why a deployment must explicitly delimit its observation scope.

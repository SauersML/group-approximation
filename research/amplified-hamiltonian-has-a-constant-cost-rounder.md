---
rg: 2
id: amplified-hamiltonian-has-a-constant-cost-rounder
kind: claim
title: The amplified Hamiltonian admits a constant-cost exactification rounder
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

Criterion (A) of the attack.  The output `H'` of the amplifier of
`locality-preserving-constant-combinatorial-gap` admits a `C`-rounder with
`C = O(1)` in the sense of
`combinatorial-gap-and-rounder-give-energy-gap`.

**This node is a pivot, not a reduction.**  By the converse half of
`combinatorial-gap-and-rounder-give-energy-gap`, the bare existence of a
constant-cost rounder for a fixed Hamiltonian is *logically equivalent* to
its energy gap being constant.  So proving this claim by any route which only
asserts that some instrument exists renames
`quantum-pcp-constant-gap-local-hamiltonian` and proves nothing.  It is kept
as a separate node only because it is the interface at which the structured
statements meet the transfer theorem.

The whole content therefore lives in the route
`rounder-from-local-ports-and-exactifier`, whose prerequisites demand that
the fault set be the outcome of a joint measurement of **commuting local**
projectors of **bounded overlap**, and that exactification be conditional on
that outcome.

## Attempts

- **Adversarial fault tolerance as the rounder.**  Recorded dead as
  `qpcp-rounder-from-adversarial-fault-tolerance`, killed by
  `whole-time-slice-corruption-costs-inverse-depth`.
- **Combinatorial soundness as the rounder.**  Recorded dead as
  `qpcp-rounder-from-combinatorial-soundness-alone`, killed by
  `coherent-shear-is-combinatorially-invisible`: on an explicit 2-local chain
  the exact fault count is `1` while the energy is `Theta(1/D)`, so no
  argument converting energy into a violated-constraint count can produce a
  constant-cost, endpoint-faithful instrument.
- **Bare existence.**  Excluded by the converse above; it is the
  restatement-dressed-as-reduction shape this graph is built to catch.

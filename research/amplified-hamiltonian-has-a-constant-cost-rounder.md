---
rg: 2
id: amplified-hamiltonian-has-a-constant-cost-rounder
kind: claim
title: The amplified Hamiltonian admits a constant-cost exactification rounder
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

Criterion (A) of the attack. Each NO-instance output `H'` of the same
amplifier used in `locality-preserving-constant-combinatorial-gap` and
`amplifier-preserves-yes-energy-below-the-floor` admits a `C`-rounder with
`C = O(1)` in the sense of
`combinatorial-gap-and-rounder-give-energy-gap`.

**This node is a pivot, not a reduction.**  By the converse half of
`combinatorial-gap-and-rounder-give-energy-gap`, on NO-instance families
with positive constant combinatorial gap, a uniform constant rounder cost
is equivalent to a uniform positive normalized energy floor. On one fixed
finite Hamiltonian some finite-cost rounder always exists, and the
frustration-free case has cost zero. Establishing a uniform bound requires
an argument; bare existence does not provide it. Nor does the equivalence
establish the hardness reduction or its YES-side promise. This node is the
interface where structured constructions meet the transfer theorem.

One construction route is
`rounder-from-local-ports-and-exactifier`, whose prerequisites demand that
the fault set be the outcome of a joint measurement of **commuting local**
projectors of **bounded overlap**, and that exactification be conditional on
that outcome. These are now bound to a single tuple by the open claim
`amplifier-has-compatible-local-syndrome-effects`; separate existential
constructions do not discharge this interface. The rounder is needed on
NO outputs for soundness. Completeness uses the separate YES energy bound.

The alternative `rounder-from-uniform-kernel-resolution` needs feasible
input support resolutions, uniform local positive spectral bounds, and
bounded occurrence. It can supply the bare rounder without an efficient
physical measurement. Its resolution construction is also open; neither
spanning the permitted subspaces nor normalizing their projectors proves it.

**2026-09-11 positive shift audit.** Every construction clause below this node
is met by the shifted standard reduction:
- the cost clause with `C=1/epsilon`;
- compatible local syndrome effects and port domination, using trivial
  single-flag ports with `C_0=1/epsilon` and `R=1`;
- the conditioned exactifier;
- the uniform kernel resolution with `delta=epsilon`;
- the anchor and backward recursion inequalities.

That reduction's YES margin is inverse polynomial. So these clauses constrain
an amplifier only jointly with
`amplifier-preserves-yes-energy-below-the-floor`, and a construction satisfying
them is not evidence toward the root unless the same reduction carries a
constant margin (`anchored-criterion-components-are-shift-satisfiable`). The
syndrome technology keeps its intended use for an amplifier that carries the
margin.

## Attempts

- **Adversarial fault tolerance as the rounder.**  Recorded dead as
  `qpcp-rounder-from-adversarial-fault-tolerance`, killed by
  `whole-time-slice-corruption-costs-inverse-depth`.
- **Combinatorial soundness as the rounder.**  Recorded dead as
  `qpcp-rounder-from-combinatorial-soundness-alone`, killed by
  `qubit-pairs-have-half-gap-and-unbounded-rounder-cost`: bounded-occurrence
  projector instances have combinatorial gap `1/2` but optimal unrestricted
  rounder cost `(N^2+1)/2`.
- **Bare existence.**  Excluded by the converse above; it is the
  restatement-dressed-as-reduction shape this graph is built to catch.

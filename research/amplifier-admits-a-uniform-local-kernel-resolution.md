---
rg: 2
id: amplifier-admits-a-uniform-local-kernel-resolution
kind: claim
title: The same amplifier's NO outputs admit feasible input support resolutions with uniform local spectra
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
distinct_from:
  kernel-resolutions-and-local-spectra-bound-rounder-cost: that proves a conditional cost bound once a resolution and local spectra are supplied; this asks for those data on the NO outputs of the actual common amplifier and is not established by the conditional theorem.
  amplifier-has-compatible-local-syndrome-effects: that requires an actual bounded-horizon physical port realization as well as compatible effects; this asks for an unrestricted kernel resolution with uniform local spectra and need not give an efficient measurement.
  amplified-hamiltonian-has-a-constant-cost-rounder: that is the general rounder interface; this is a specific sufficient construction through local input supports and spectral bounds.
---

For every NO output of the **same** polynomial-time amplifier used for the
constant combinatorial gap and YES energy margin, supply neighborhoods
with bounded occurrence `R`, a uniform `delta>0`, and positive effects
`T_S` with the following simultaneous properties:

1. They sum to `I` and vanish for every infeasible fault set.
2. For feasible `S`, their ranges lie in
   `intersection_(a in S) ran(A_a)`, where `A_a` is that neighborhood sum.
3. `A_a>=delta P_(ran A_a)` for every label and instance.

One possible way to meet clause 3 is a fixed finite collection of term
matrices with bounded locality, dimension, and neighborhood cardinality.
That hypothesis must be proved for the amplifier, not inferred from its
constant local dimension. This claim demands no efficient measurement or
input-preserving recovery; the bare rounder interface does not need them.

## Attempts

- **Normalize a spanning family of support projectors.** Invertibility of
  their sum is insufficient: normalization rotates the nonorthogonal
  pair's supports and produces strictly positive cost on a zero-energy
  input for one local term. The artifact gives the exact rational failure.
- **Use support-preserving normalization.** It works if the sum is
  invertible and commutes with every allowed support projection. No such
  family with globally feasible labels is supplied for the amplifier.
- **Use a finite term collection to get everything.** This supplies the
  local spectral bound only. The globally feasible identity resolution and
  the completeness-preserving amplifier are still missing.
  `fixed-term-chain-defeats-bounded-syndrome-neighborhoods` now gives a
  fixed-matrix counterexample to this generic inference, even allowing
  arbitrary global measurements and any finite local charge constant.
  Its gap is not a constant combinatorial gap, so the actual amplifier
  construction remains open.
- **Prepare independent random flags.** A nonzero marginal `p_a I` needs
  `A_a` invertible. If all neighborhood sums are singular in a frustrated
  instance, this forces all flags to vanish and fails joint feasibility.

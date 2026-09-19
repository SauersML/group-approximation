---
rg: 2
id: constant-repetition-disjoint-tag-ledger-proof
kind: route
title: Repeat the five-fourths source until it exceeds ambient tag capacity
target: constant-repetition-v4-needs-only-disjoint-tags
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
  - disjoint-tag-covariance-controls-cross-gram
  - gram-branching-capacity-with-overlap
---

Duplicate the finitely many context packets `L` times, sharing the original
BCS selector tuple. Since `L` is fixed, word telescoping and packet
exactification losses remain a fixed multiple of the defining energy. In
each copy, `(VOF5)` makes the sum of the three failure traces `5/4` times its
forbidden carrier trace. Splitting a failure projection into its orthogonal
radical atoms does not change this sum, proving `(CRV2)`.

Apply the disjoint-tag theorem to all ordered pairs. It bounds their complete
cross-Gram energy by `C_1E_rel`. In the Gram capacity theorem take the target
projection to be the identity of the common ambient amplification. Its
leakage term is zero and its normalized trace is `M_0`; `(GBC2)` is exactly
`(CRV3)`. Substitute `q>=beta-E_base`, enlarge both error coefficients to
one `E`, and rearrange to obtain `(CRV5)`.

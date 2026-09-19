---
rg: 2
id: constant-repetition-pairwise-antiphase-ledger-proof
kind: route
title: Insert the pairwise antiphase estimate into ambient V4 capacity
target: constant-repetition-v4-needs-only-pairwise-antiphase
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
  - pairwise-antiphase-covariance-controls-cross-gram
  - gram-branching-capacity-with-overlap
---

Fixed repetition and the V4 five-fourths identity give `(PAV1)--(PAV2)` by
the same trace accounting as the disjoint-tag ledger.  The pairwise
antiphase theorem and `(PAV3)` bound the ordered cross-Gram term `o` in
`(GBC2)` by `C_pair E_rel`.  Taking the target projection to be the identity
sets leakage to zero and target capacity to `M_0`, proving `(PAV4)`.

Substitute `q>=beta-E_base` into `(PAV4)`, enlarge both nonnegative error
terms to `E=E_base+E_rel`, and rearrange.  The numerator is positive by
`(PAV5)`, yielding `(PAV6)`.

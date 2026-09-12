---
rg: 2
id: deligne-sep7-norm-parameter-closed-subgroup-proof
kind: route
title: Tensor and diagonalize point-norm models and insert an exact metaplectic sector
target: deligne-sep7-norm-parameter-closed-subgroup
requires:
  - maslov-mod3-gap-is-metaplectic-base-degree-six-gap
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
---

Tensor products add the multiplier parameters, with the operator defect of
the tensor product bounded by the sum of the two defects. Complex
conjugation negates a parameter, and the trivial representation supplies
zero. These operations show that `P_op` is a subgroup.

If `theta_n->theta`, choose a `theta_n` model with defect below `1/n` on
the first `n` multiplication pairs in a fixed enumeration of `Gamma^2`.
For each fixed pair the multiplier phases converge, so these chosen tuples
form a point-norm model at `theta`. This proves closedness.

The required claim states that the metaplectic double cover `E_2` is
residually finite. A finite quotient detecting its central involution has
a nonzero negative central spectral summand in its regular representation.
Restricting a section of `Gamma` to that summand gives an exact
`c_(1/2)`-projective representation. Thus `1/2 in P_op`.
Classification of closed subgroups of the circle gives the assertion,
including the evenness of a finite subgroup's order. The artifact provides
the detailed construction and fixes the cocycle normalization.

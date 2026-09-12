---
rg: 2
id: substituted-elementary-not-infranormal-proof
kind: route
title: Compressors normalize M_r(S) by a discriminant count, and e_12(f) does not
target: substituted-elementary-subgroup-is-not-infranormal
requires: []
---

1. If `gamma EL_r(S) gamma^(-1) <= EL_r(S)`, then
   `gamma E_ij gamma^(-1) = gamma (I + E_ij) gamma^(-1) - I` lies in `M_r(S)`
   for `i != j`, and `E_ii = E_ij E_ji`. By `S`-linearity,
   `gamma M_r(S) gamma^(-1) <= M_r(S)`.
2. The two lattices have the same trace Gram matrix, with unit discriminant.
   So the change-of-basis determinant is a unit, and the inclusion is
   equality. The normalizer is a group containing the compression semigroup,
   and hence the group it generates.
3. `e_12(f) E_21 e_12(-f) = E_21 + f E_11 - f E_22 - f^2 E_12`, which has
   entry `f`. So `e_12(f)` is not in the normalizer when `f` is outside `S`.

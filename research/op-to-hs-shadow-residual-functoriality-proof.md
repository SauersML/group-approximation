---
rg: 2
id: op-to-hs-shadow-residual-functoriality-proof
kind: route
title: Intersect the HS-shadow kernels and restrict target microstates
target: op-to-hs-shadow-residual-functoriality
requires: []
artifacts:
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

Each operator-norm almost representation and cofinite ultrafilter gives an
honest normalized-HS ultraproduct homomorphism.  Intersecting their kernels
gives a normal subgroup.  Given `f:G->H`, precompose an almost representation
of `H` with `f`; this proves `f(S(G)) <= S(H)`.  Normality then contains the
normal closure of every member.  Lean checks these statements as
`opToHSShadowResidual_normal`, `map_opToHSShadowResidual_le`, and
`normalClosure_le_opToHSShadowResidual`.

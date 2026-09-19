---
rg: 2
id: exact-projective-codensity-trace-square-gap-proof
kind: route
title: Cancel projective phases by perfectness, then apply the Kazhdan projection and co-density
target: exact-projective-codensity-has-a-uniform-trace-square-gap
requires: []
---

The proof is the calculation `(EPT4)--(EPT11)` in the target claim.  The
cocycle `w_g=U rho(g)U* rho(g)*` is close on generators to scalar phases.
Writing each generator of the perfect group `C` as one fixed product of
commutators cancels those phases and bounds its ordinary commutator defect by
`L sqrt(2E)`.  Property (T) moves `U` within
`L sqrt(2E)/kappa` of `rho(C)'`; co-density identifies this with `rho(A)'`.
Commuting the projection with `rho(h)` and applying
`1-|tr(v)|^2 <= ||v-I||_2^2` yields `(EPT2)` with
`K=8L^2/kappa^2`, uniformly in dimension.


---
rg: 2
id: leavitt-branch-reynolds-gap-proof
kind: route
title: Intersect the transported source commutant with the transverse child commutant
target: leavitt-branch-reynolds-return-has-rectangular-gap
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - weyl-commutant-superrank-detects-rectangular-return
---

Branch covariance gives `(BRG2)`.  The child adjoint actions commute, so
their Reynolds expectations commute and `(BRG1)` holds.  Compressing the
transported source range by `R_1` gives `(BRG3)`.  Cyclicity then identifies
its squared Gram trace with `tr_ad(R_0R_1)=p^(-4)`, while the transported
source range has trace `p^(-2)`.  Pythagoras gives `(BRG5)`.

For `(BRG6)`, write the retained Gram trace as
`tr_ad(R_1VR_sV^*R_1)` and replace `VR_sV^*` by `R_0`; multiplication by
orthogonal projections is HS-contractive.  Subtract the resulting upper
bound from `tr_ad(R_s)=p^(-2)`.

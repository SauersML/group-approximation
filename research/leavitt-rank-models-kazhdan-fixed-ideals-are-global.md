---
rg: 2
id: leavitt-rank-models-kazhdan-fixed-ideals-are-global
kind: claim
title: In every rank model of the Leavitt unit group the compressed Kazhdan subgroup fixes exactly what the whole group fixes, in every tensor degree
distinct_from:
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open existence of F_2-linear models of the same group; this is a necessary condition that every rank model, over any field, meets.
  rank-ultraproduct-compressors-conserve-fixed-right-ideals: that is the general conservation theorem for compressed finitely generated subgroups; this is its instance for the nine-leaf configuration, where simplicity makes the normal closure the whole group.
artifacts:
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)` and `Gamma = EL_alpha(R) <= G_L = EL_D(R) = R^x`
be the nine-leaf configuration. For every field `k`, every rank ultraproduct `M` over
`k`, every homomorphism `sigma : R^x -> M^x` and every tensor degree `(a,b)`,

    Fix^(a,b)(sigma(Gamma)) = Fix^(a,b)(sigma(R^x)).

In degree `(1,1)`, the linear-scale part of the commutant of `sigma(Gamma)` equals that of
`sigma(R^x)`. The same holds for every nontrivial finitely generated subgroup of `R^x`
whose compressors generate `R^x`.

So a model where the Kazhdan subgroup fixes a linear-size subspace, or has a linear-size
commutant, that the whole group does not, is excluded, whatever the field. This is a
necessary condition for `binary-leavitt-unit-group-is-f2-linear-sofic`, not a
construction.

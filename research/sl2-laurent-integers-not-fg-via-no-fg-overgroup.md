---
rg: 2
id: sl2-laurent-integers-not-fg-via-no-fg-overgroup
kind: route
title: "If SL_2(Z[t]) has no finitely generated overgroup in SL_2(Q(t)), SL_2(Z[t,t^-1]) is not finitely generated"
target: sl2-laurent-integers-is-not-finitely-generated
requires:
  - sl2-polynomial-integers-in-no-fg-subgroup-of-sl2-rational
---

`SL_2(Z[t]) ⊂ SL_2(Z[t,t^{-1}]) ⊂ SL_2(Q(t))`. If `SL_2(Z[t,t^{-1}])` were finitely
generated, it would be a finitely generated subgroup of `SL_2(Q(t))` containing
`SL_2(Z[t])`, contradicting `sl2-polynomial-integers-in-no-fg-subgroup-of-sl2-rational`.

---
rg: 2
id: f-infinity-fcd-type-f-from-contractible-rips
kind: route
title: Yes to Problem 4.6 gives yes to Problem 1.21 through the free cocompact action on a contractible Rips complex
target: f-infinity-groups-of-finite-cd-are-of-type-f
requires:
  - f-infinity-finite-cd-groups-have-contractible-rips
  - contractible-rips-complex-gives-finite-classifying-space
---

Let `G` be of type `F_∞` with `cd G < ∞`. It is torsion-free, since finite
cohomological dimension excludes nontrivial finite subgroups. By
`f-infinity-finite-cd-groups-have-contractible-rips`, some `R_r(G,S)` is
contractible. By `contractible-rips-complex-gives-finite-classifying-space`,
`R_r(G,S)/G` is a finite `K(G,1)`, so `G` is of type F. This is the remark printed
in Zaremsky Problem 4.6 ("This would imply it's of type F, so this would solve
Problem 21"). The cycle with `f-infinity-fcd-contractible-rips-from-1-21-and-4-07`
is intended.

---
rg: 2
id: no-contractible-rips-from-f-infinity-group-not-of-type-f
kind: route
title: A counterexample to Problem 1.21 has no contractible Rips complex, so it answers Problem 4.6 no
target: some-f-infinity-finite-cd-group-has-no-contractible-rips
requires:
  - some-f-infinity-group-of-finite-cd-is-not-of-type-f
  - contractible-rips-complex-gives-finite-classifying-space
---

Let `G` be of type `F_∞` with `cd G < ∞` and not of type F
(`some-f-infinity-group-of-finite-cd-is-not-of-type-f`). `G` is torsion-free. If
some `R_r(G,S)` were contractible,
`contractible-rips-complex-gives-finite-classifying-space` would make `G` of type
F. So no Rips complex of `G`, for any finite generating set and any scale, is
contractible, and `G` witnesses the target.

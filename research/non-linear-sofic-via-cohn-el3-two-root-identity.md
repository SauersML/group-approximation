---
rg: 2
id: non-linear-sofic-via-cohn-el3-two-root-identity
kind: route
title: The Cohn-coefficient two-root identity makes EL_3 over the binary Leavitt algebra not F_2-linear sofic
target: non-linear-sofic-group
requires: [cohn-coefficient-el3-rank-models-satisfy-two-root-identity, reversed-root-pair-identity-forces-root-squares-to-vanish, el3-unit-root-matrix-units-iff-two-root-identities, matrix-unit-rank-models-extract-ring-rank-models, leavitt-algebra-has-no-unital-rank-model]
artifacts:
  - research/artifacts/gottschalk-region-synthesis-2026-09-12.md
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

Wiring. Commit 013740e0d records the chain "Jacobson radical => Cohn identity => R^x has no nontrivial
model". The first arrow is `cohn-el3-two-root-identity-from-jacobson-rank-radical`. The second arrow had no
route on main. The argument is the paragraph "Why it calibrates the gate" on the Cohn node, taken as a route.

1. Let `C_2 = <s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>` over `F_2` and `q = 1 - s_0 t_0 - s_1 t_1`, so
   `C_2 / (q) = R = L_(F_2)(1,2)`. The quotient map is onto, so `EL_3(C_2) -> EL_3(R)` is onto: each
   generator `x_ab(r)` lifts to some `x_ab(r~)`.
2. Let `sigma : EL_3(R) -> M^x` be a characteristic-two rank model. Its pullback to `EL_3(C_2)` has the same
   images of `x_12(1)` and `x_23(1)`, so the same product `N_23 N_12`. The first requirement makes it `0`.
3. `reversed-root-pair-identity-forces-root-squares-to-vanish` gives `N_ab^2 = 0` for every root. With both
   identities, `el3-unit-root-matrix-units-iff-two-root-identities` makes the unit root elements act by matrix
   units.
4. `matrix-unit-rank-models-extract-ring-rank-models` gives a rank model of `R`, unless `sigma` is trivial.
   `leavitt-algebra-has-no-unital-rank-model` excludes a rank model of `R`.
5. So every characteristic-two rank model of `EL_3(R)` is trivial. `EL_3(R)` is countable and infinite, so it
   has no injective model and is not linear sofic over any field of characteristic two. This witnesses
   `non-linear-sofic-group` with `F = F_2`.

No mathematics is added beyond the named nodes. The Cohn claim is open, so the route does not fire.

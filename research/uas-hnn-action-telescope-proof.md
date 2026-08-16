---
rg: 2
id: uas-hnn-action-telescope-proof
kind: route
title: Restrict to the levels, take the union, then adjoin the stable letter
target: uas-base-gives-sofic-hnn-coset-action
requires: []
artifacts:
  - GroupApproximation/Sofic/AscendingHNNCosetActionSofic.lean
  - GroupApproximation/Sofic/CoAmenableActionSofic.lean
  - GroupApproximation/Sofic/SoficActionOrbits.lean
  - GroupApproximation/Sofic/GeneralizedWreathSofic.lean
---

## Why sufficient

**The implication chain.**  A strongly co-amenable subgroup has coset action
factoring through an amenable quotient, and every action of an amenable group
is sofic: a Folner set invariant under the finite test window gives an exact
partial-multiplication model, with charts `pi_a(y) = a^-1 y` into the finite
target `{a^-1 y}`.  Chabauty limits of sofic transitive actions are sofic
(finitely many membership tests survive the limit), orbits glue by taking
products of models over the finitely many orbits met, and an arbitrary
stabilizer is an increasing limit of finitely generated ones.  That is LERA
=> UAS, with LERF => LERA because finite-index subgroups are strongly
co-amenable.  UAS => sofic because a sofic left-regular *action* forces
`phi(g)` to be almost fixed-point free: a fixed good point would give
`pi_s(1) = pi_s(g^-1)` against injectivity of the chart.

**The HNN argument.**  Put `Gamma_n = t^-n Gamma t^n` and `N = union
Gamma_n`, so `Gamma_0 <= Gamma_1 <= ...` and `G = N x| <t>`.  Each level is
isomorphic to `Gamma`, hence UAS, so each restricted action on `G/Gamma` is
sofic; a finite control set in `N` lies in one level, so the union action is
sofic.  Adjoining the stable letter is the cyclic-extension permanence
theorem: stack `L` translated copies of an `N`-model around a cycle, define
`Phi(n t^q) = P(n) T^q` with `P(n)` acting on level `j` through
`beta^-j(n)`, charts `pi_(j,a)(x) = rho_a(t^-j x)`, and good levels those at
distance more than `Q` from the cyclic seam.  At most `2Q` of the `L` levels
are seam levels, so the multiplicativity defect is at most `2Q/L + delta`, and
on a good level the covariance identity is exact because
`(beta^-k(n))^-1 t^-k = t^-k n^-1`.

The wreath conclusion is the generalized wreath theorem: soficity of the
action supplies the orbit charts, soficity of the lamp makes each finite
coordinate group `K^(B_i)` sofic, and soficity of the acting group is used
only at the final embedding of `W` into `(W / ker rho) x G`.

`AscendingHNNCosetActionSofic.lean` carries `UniversallyActionSofic` and
`isSoficAction_vertical_cosets_of_uas`; `CoAmenableActionSofic.lean` carries
the strongly co-amenable and LERA cases; `SoficActionOrbits.lean` the orbit
gluing; `GeneralizedWreathSofic.lean` the wreath step.

## Ancestry

The LERF case is Gao's theorem (arXiv:2402.17150) and the wreath permanence is
Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.6 (arXiv:2401.04945); both are
reproved rather than imported in sections 29--30 of the dossier, and the
in-repo Lean is independent of them.  The LERA extension and the HNN
consequence are the additions.

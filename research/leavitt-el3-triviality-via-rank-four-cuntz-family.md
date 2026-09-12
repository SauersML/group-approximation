---
rg: 2
id: leavitt-el3-triviality-via-rank-four-cuntz-family
kind: route
title: A corner Leavitt family from the fourth index, with no ring rank model, trivializes EL_3 rank models
target: leavitt-el3-rank-models-over-finite-fields-are-trivial
requires:
  - rank-four-isometry-relations-give-corner-cuntz-family
  - leavitt-algebra-has-no-unital-rank-model
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
artifacts:
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
---

Let `K` be a finite field of characteristic `p`, `R = L_K(1,2)`, and `sigma : EL_3(R) -> M^x` a rank
model into a characteristic-`p` rank ultraproduct. `EL_3(R)` is a subgroup of `R^x = EL_4(R)`, and
by `leavitt-gl-equals-el-and-perfect-unit-group` the two coincide for `R`, so `sigma` is a rank
model of `R^x`. Put `D = N_23 N_12`.

* If `D = 0`, then in characteristic two `N_12^2 = 0` is automatic and
  `el3-unit-root-matrix-units-iff-two-root-identities` makes the six unit root elements act by
  matrix units; `matrix-unit-rank-models-extract-ring-rank-models` then extracts a unital ring
  homomorphism `R -> p_1 M p_1`, or `sigma` is trivial. The first is excluded by
  `leavitt-algebra-has-no-unital-rank-model`. So `sigma` is trivial.
* If `D != 0`, then `rank-four-isometry-relations-give-corner-cuntz-family` gives an order-two
  Leavitt family in a corner `eMe` with `rk(e) > 0`, i.e. a unital homomorphism `R -> eMe` into a
  rank ultraproduct, again excluded by `leavitt-algebra-has-no-unital-rank-model`. So this case does
  not occur.

Either way `sigma` is trivial, which is `leavitt-el3-rank-models-over-finite-fields-are-trivial` for
`R = L_K(1,2)`. The odd-characteristic case adds only the `p`-nilpotent bookkeeping for
`N_12^p = 0`; the assembly is characteristic-uniform. The route is valid once the single open
prerequisite `rank-four-isometry-relations-give-corner-cuntz-family` is established; the other three
requirements are established.

**Minimal form of the second case (lead pass, family R4).** The contradiction uses only
`T_0 S_0 = e = T_1 S_1` and `T_1 S_0 = 0` in `eMe` with `e != 0`. Then `(T_0 + 1 - e)(S_0 + 1 - e) = 1`,
and direct finiteness of `M` gives `S_0 T_0 = e`, so `T_1 = T_1 S_0 T_0 = 0` and `e = T_1 S_1 = 0`.
Completeness `S_0 T_0 + S_1 T_1 = e` is not used. Artifact Section L1.

Payoff: through the target's own routes, `non-linear-sofic-group` for `K = F_2`, `n = 2`, and the
non-`F_p`-linear-soficity of `R^x` and of `PG`.

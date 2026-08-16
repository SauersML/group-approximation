---
rg: 2
id: finite-residual-transports-across-commensurability-proof
kind: route
title: Intrinsic definition plus the finite-index membership criterion
target: finite-residual-transports-across-commensurability
requires: []
artifacts:
  - GroupApproximation/Algebra/FiniteResidualCommensurability.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise.

- `finiteResidual_eq_subgroupOf` — Lemma 49.4 in subgroup form:
  `finiteResidual K = (finiteResidual G).subgroupOf K` for `[K.FiniteIndex]`.
  Proved pointwise from `mem_finiteResidual_subgroup_iff`, the membership
  criterion already in `Algebra/FiniteResidual`, which is where the finite-index
  hypothesis is consumed.
- `map_finiteResidual_eq` — an isomorphism maps the residual onto the residual.
  One inclusion is `map_finiteResidual_le`, functoriality of the residual along
  any homomorphism (50.1); the other is that inclusion applied to the inverse
  isomorphism, which is exactly why an *isomorphism* is needed and a surjection
  would not do.
- `mulEquivFiniteResidual` — the induced isomorphism `Res_fin(G) ≅ Res_fin(H)`,
  built from the previous item as an equivalence of subgroups rather than a mere
  equality of images, which is the form the separation argument uses.
- `not_mulEquiv_of_finiteResidual_not_mulEquiv` — the contrapositive: no
  isomorphism `G ≅ H` if the residuals are non-isomorphic.
- `not_commensurable_of_finiteResidual_not_mulEquiv` — the finite-index version:
  combine the previous item with the first, so that a hypothetical isomorphism
  between finite-index subgroups would give an isomorphism of the ambient
  residuals.

## Scope

"Commensurable" here means the concrete relation the application needs — some
finite-index subgroup of one is isomorphic to some finite-index subgroup of the
other — and nothing about a commensurator or a commensurability *group* is
claimed or used.  The statements are for arbitrary groups; no finite generation,
residual finiteness, or countability appears anywhere in the chain.

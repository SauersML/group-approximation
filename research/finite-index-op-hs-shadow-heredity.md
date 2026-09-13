---
rg: 2
id: finite-index-op-hs-shadow-heredity
kind: claim
title: The operator-to-HS shadow restricts exactly to finite-index subgroups
distinct_from:
  op-to-hs-shadow-residual-functoriality: that gives one-sided functoriality; this gives equality for a finite-index inclusion.
  corona-finite-index-radical-heredity: that concerns operator-norm invisibility; this concerns universal normalized-HS invisibility of operator-norm models.
artifacts:
  - research/artifacts/infranormal-mf-detection-2026-09-13.md
---

For countable `G` and a finite-index subgroup `H`, let `S(G)` be the
subgroup of elements tending to the identity in normalized HS norm in
every operator-norm asymptotic unitary representation of `G`. Then

`S(H) = H intersect S(G)`.

For index `m`, finite induction has the quantitative estimate
`||Ind(V_n)(h)-I||_2^2 >= ||V_n(h)-I||_2^2/m` for every `h in H`.
No property (T) or normality is assumed. Mathematical proof only;
no new Lean declaration is asserted.

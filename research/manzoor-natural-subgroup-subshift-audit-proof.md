---
rg: 2
id: manzoor-natural-subgroup-subshift-audit-proof
kind: route
title: Audit the subgroup indicator, pseudo-subgroup tower, and labeled Schreier realization
target: manzoor-natural-subgroup-subshift-is-not-a-haar-envelope
requires:
  - manzoor-separation-does-not-specify-haar-cylinders
  - random-coset-lamp-correlations-realize-every-irs-character
---

The identity coordinate and inverse-pair equations prove that the support in
`(MSH1)` is neither a subgroup of the ambient Bernoulli compact group nor a
positive-measure Haar subspace.  Equation `(MSH3)` follows immediately from
the definition of the conjugation action: `g` fixes `H` exactly when
`gHg^(-1)=H`.

Manzoor's proof of Theorem 3.6 takes independent maximizers in the nested
compact feasibility sets and passes to a weak-star cluster point.  It only
uses restriction to prove monotonicity of the optimal values; it gives no
compatible family of finite actions or probability-space factor maps.
Theorem 3.13 and the final extremal separation add the two further
existential choices recorded in
`manzoor-separation-does-not-specify-haar-cylinders`.

In the AGV realization, conditioning on `H` gives the product labeling space
on the countable set `F/H`.  Varying `H` gives a measurable field of these
spaces.  The base `mu` remains a factor and neither the coordinate sets nor
the compact fiber groups have been identified with one fixed algebraic
`F`-module.  The fixed-fiber computation of
`random-coset-lamp-correlations-realize-every-irs-character` therefore does
not remove the base or produce a single group factor.  These three direct
audits prove the claim.


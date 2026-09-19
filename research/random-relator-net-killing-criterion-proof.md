---
rg: 2
id: random-relator-net-killing-criterion-proof
kind: route
title: Union-bound proof of the random-relator net-killing criterion
target: random-relator-net-killing-criterion
requires: []
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

For one net point `U`, independence of the `m` sampled relators makes the
probability that all relators have `2 eps`-small normalized-HS defect exactly
`p_n(U)^m`.  The union bound over all net points in all matrix dimensions is
therefore strictly smaller than `Pr(SC)`.  Hence some sampled relator tuple is
in `SC` and has no bad net point.

If an actual separated tuple had every relator defect at most `eps`, choose an
`eta`-near net point.  Word evaluation is `L`-Lipschitz in the bi-invariant
normalized-HS metric by telescoping, so every sampled relator would have defect
at most `eps+L eta<2 eps` at that net point, contradiction.

Finally, because `SC` keeps the finite test words distinct, Pestov's finite
almost-homomorphism characterization of hyperlinearity would, for sufficiently
small finite-table error, produce exactly such a separated generator tuple.
Thus the chosen presentation is nonhyperlinear.

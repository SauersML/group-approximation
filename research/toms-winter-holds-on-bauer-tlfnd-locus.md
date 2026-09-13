---
rg: 2
id: toms-winter-holds-on-bauer-tlfnd-locus
kind: claim
title: Strict comparison forces Z-stability for unital simple separable nuclear algebras with Bauer trace simplex and tracially locally finite nuclear dimension
distinct_from:
  stw18-unital-toms-winter: that is the unital Toms--Winter conjecture on every trace simplex; this is its Bauer-simplex case under tracially locally finite nuclear dimension.
  toms-winter-holds-on-tlfnd-rank-density-locus: that proves the implication under bounded rank density on any simplex; this imposes no rank density hypothesis and restricts the simplex to Bauer.
  stw18-finite-trace-boundary-toms-winter: that is the established case of compact finite-dimensional extreme boundary; this allows every compact extreme boundary.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a nontrivial hyperfinite W*-bundle with no comparison hypothesis; this is the positive Toms--Winter statement on Bauer simplices, where every counterexample yields such a bundle.
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra whose trace simplex is a nonempty Bauer simplex, with tracially locally
finite nuclear dimension. If `A` has strict comparison of positive elements, then
`A ≅ A ⊗ Z`.

No nuclear algebra without locally finite nuclear dimension is known (Vaccaro,
arXiv:2604.24682v2), so among known examples this is Toms–Winter on Bauer simplices.

**Known cells.**
- Compact finite-dimensional extreme boundary: `stw18-finite-trace-boundary-toms-winter`.
- Countable-dimensional extreme boundary, through uniform Gamma:
  `r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`.
- Bounded rank density: `toms-winter-holds-on-tlfnd-rank-density-locus`.
- A unital simple infinite-dimensional unique-trace subalgebra, or unital
  `Z_{n,n+1}` for large `n`: `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`.

**Route.** `toms-winter-bauer-tlfnd-via-divisible-unit` reduces this claim to
`strict-comparison-forces-tracially-divisible-unit`.

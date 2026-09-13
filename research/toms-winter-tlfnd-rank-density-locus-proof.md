---
rg: 2
id: toms-winter-tlfnd-rank-density-locus-proof
kind: route
title: Strict comparison gives projection comparison, division and support projections, hence uniform Gamma under tracial dimension control, hence Z-stability
target: toms-winter-holds-on-tlfnd-rank-density-locus
requires:
  - strict-comparison-compares-ultrapower-projections
  - ultrapower-comparison-with-rank-density-divides-projections
  - strict-comparison-with-rank-density-gives-support-projections
  - uniform-gamma-iff-tracial-support-projections-and-division
  - uniform-gamma-algebras-satisfy-toms-winter
artifacts:
  - research/artifacts/tw-support-gap-crux-2026-09-12.md
---

Assume `A` is unital, simple, separable, nuclear and non-elementary, with
`T(A) ≠ ∅`, tracially locally finite nuclear dimension, RD_b and strict
comparison.

1. **PC.** `strict-comparison-compares-ultrapower-projections` gives projection
   comparison by limit traces in every `M_k(A^U)`.
2. **PD.** With RD_b, `ultrapower-comparison-with-rank-density-divides-projections`
   gives a unital `M_n` in every projection corner of every `M_k(A^U)`.
3. **TSP.** `strict-comparison-with-rank-density-gives-support-projections`
   gives `γ_A(a) = 0` for every positive contraction `a`.
4. **Gamma.** Part (b) of `uniform-gamma-iff-tracial-support-projections-and-division`
   turns TSP and PD into uniform property Gamma under tracially locally finite
   nuclear dimension.
5. **Z-stability.** `uniform-gamma-algebras-satisfy-toms-winter` (CETW
   arXiv:1912.04207, Theorem A) turns uniform Gamma and strict comparison into
   Z-stability and finite nuclear dimension.

Every hypothesis of each cited claim is among the standing assumptions: unital,
simple, separable, nuclear, non-elementary, `T(A) ≠ ∅`, strict comparison, RD_b
and tracially locally finite nuclear dimension.

---
rg: 2
id: toms-winter-bauer-tlfnd-via-bundle-halving
kind: route
title: If every hyperfinite W*-bundle divides its unit uniformly, the strict closure divides the unit of A, and Toms-Winter follows on Bauer simplices with tlfnd
target: toms-winter-holds-on-bauer-tlfnd-locus
requires: [toms-winter-bauer-tlfnd-iff-tracially-divisible-unit, bauer-uniform-gamma-iff-trivial-tracial-bundle, r-fibre-w-star-bundles-divide-the-unit-uniformly]
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

Let `A` be unital, simple, separable, nuclear and non-elementary, with Bauer `T(A)`,
tlfnd and strict comparison. Put `K = ∂_e T(A)`.

1. **The bundle.** By `bauer-uniform-gamma-iff-trivial-tracial-bundle`, the strict
   closure `M` of `A` is a strictly separable continuous W*-bundle over `K` with every
   fibre `R`.
2. **Division in `M`.** `r-fibre-w-star-bundles-divide-the-unit-uniformly` (open) gives
   order zero `φ_m: M_N → M` with `‖E(1 − φ_m(1))‖ → 0`, hence a unital `M_N → M^U`.
3. **Back to `A`.** The unit ball of `A` is `‖·‖_{2,u}`-dense in that of `M`, since
   `A^u = A^st` (Ozawa, arXiv:1304.3523, read on MSI). So `M^U = A^U`, and condition
   (d) of `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit` holds.
4. **Conclusion.** That theorem gives `A ≅ A ⊗ Z`.

Step 2 is the only open input.

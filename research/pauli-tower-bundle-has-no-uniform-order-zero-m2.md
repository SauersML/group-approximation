---
rg: 2
id: pauli-tower-bundle-has-no-uniform-order-zero-m2
kind: claim
title: The Pauli tower's R-fibre W*-bundle admits no order zero M_2 whose unit has trace above 3/4 at every point
distinct_from:
  r-fibre-w-star-bundles-divide-the-unit-uniformly: that asserts uniformly large order zero M_N in every R-fibre bundle for every N; this is a counterexample at N = 2.
  pauli-tower-bundle-has-scalar-point-property: that is the scalar point property; this is its consequence for order zero maps, through the variance of the image of a minimal projection.
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

**Statement (unreviewed).** Let `M` be the W*-bundle of `pauli-tower-bundle-has-scalar-point-property`,
over `X̂` with conditional expectation `E`. There is no c.p.c. order zero map `φ: M_2 → M` with
`‖E(1 − φ(1))‖ < 1/4`. Equivalently, the reduced power `M^U` contains no unital copy of `M_2`.

**So `r-fibre-w-star-bundles-divide-the-unit-uniformly` is false.**

**Consequences.**
- **Dead route.** `toms-winter-bauer-tlfnd-via-bundle-halving` cannot fire. Its bundle premise fails
  for this abstract bundle.
  - The crux `strict-comparison-forces-tracially-divisible-unit` is untouched: `A` is not simple,
    and strict comparison was not examined.
- **Z-stability fails.** `A ≅ A ⊗ Z` would give such maps, from the unique trace of `Z`. So the
  algebra of the Pauli tower is not Z-stable.
- **The obstruction is at the unit.** In `M_2(M)`, `e_{11} ⊗ 1` has constant normalized trace `1/2`.
  - A strict-comparison witness to the crux of this shape would also need to exclude constant rank
    windows in every `M_k(A)`.
  - The reason is `strict-comparison-unit-divisibility-equivalences`: under strict comparison, rank
    windows give unit division.

Proof: route `pauli-tower-bundle-has-no-uniform-order-zero-m2-proof`.

---
rg: 2
id: pauli-tower-bundle-has-no-uniform-order-zero-m2
kind: claim
title: Every order zero copy of M_2 in the Pauli tower's R-fibre W*-bundle vanishes in some fibre
distinct_from:
  r-fibre-w-star-bundles-divide-the-unit-uniformly: that asserts uniformly large order zero M_N in every R-fibre bundle for every N; this is a counterexample at N = 2.
  pauli-tower-bundle-has-scalar-point-property: that is the scalar point property; this is its consequence for orthogonal pairs and order zero maps.
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-part2-2026-09-13.md
---

**Statement (review PASS, part 9 §9.6 of `research/artifacts/ex-review2-analysis-2026-09-13-part9.md`).** Let `M` be the W*-bundle of `pauli-tower-bundle-has-scalar-point-property`,
over `X̂` with conditional expectation `E`.
- **Orthogonal pairs.** For positive `a, b ∈ M` with `ab = 0`, some `λ ∈ X̂` has `π_λ(a) = 0` or
  `π_λ(b) = 0`.
- **Order zero maps.** Every c.p.c. order zero `φ: M_N → M` with `N ≥ 2` has a point `λ` with
  `π_λ ∘ φ = 0`. So `min_λ τ_λ(φ(1)) = 0`.
- **Projections.** Every projection of `M` is `0` or `1` in some fibre.
- **Reduced power.** `M^U` contains no unital copy of `M_2`. The weaker form proved first was:
  no `φ` with `‖E(1 − φ(1))‖ < 1/4`.

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

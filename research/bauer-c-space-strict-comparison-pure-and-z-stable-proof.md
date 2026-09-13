---
rg: 2
id: bauer-c-space-strict-comparison-pure-and-z-stable-proof
kind: route
title: Divide the unit over the C-space boundary, then apply the Bauer purity and Z-stability equivalences
target: bauer-c-space-strict-comparison-pure-and-z-stable
requires:
  - bauer-c-space-strict-comparison-divides-unit
  - bauer-strict-comparison-pure-iff-divisible-unit
  - toms-winter-bauer-tlfnd-iff-tracially-divisible-unit
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

1. `bauer-c-space-strict-comparison-divides-unit` makes the unit tracially
   `N`-divisible for every `N`. This is item (e) of both equivalence theorems below.
2. **(a)** `bauer-strict-comparison-pure-iff-divisible-unit` (exact, Bauer, strict
   comparison): (e) ⟹ (a) gives purity.
3. **(b)** With nuclearity and tracially locally finite nuclear dimension,
   `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`: (e) ⟹ (a) gives
   `A ≅ A ⊗ Z`. ∎

---
rg: 2
id: stw18-unital-toms-winter-via-tracial-comparison
kind: route
title: Strict comparison compares ultrapower projections, comparison would give Gamma, and Gamma gives Z-stability
target: stw18-unital-toms-winter
requires:
  - strict-comparison-compares-ultrapower-projections
  - tracial-projection-comparison-forces-uniform-gamma
  - uniform-gamma-algebras-satisfy-toms-winter
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

Let `A` be unital, simple, separable, nuclear, non-elementary with strict
comparison.  If `T(A)` is empty, `A` is purely infinite and O_infinity-stable.
Otherwise:

1. `strict-comparison-compares-ultrapower-projections` (nuclear algebras are
   exact) gives comparison of projections by limit traces in every
   `M_k(A^omega)`.
2. `tracial-projection-comparison-forces-uniform-gamma` then gives uniform
   property Gamma.
3. `uniform-gamma-algebras-satisfy-toms-winter` turns strict comparison plus
   uniform Gamma into Z-stability.

Step 2 is the only open input.  The route isolates it as a statement about
tracial ultrapowers alone: the C*-algebraic comparison hypothesis has been
used up in step 1.

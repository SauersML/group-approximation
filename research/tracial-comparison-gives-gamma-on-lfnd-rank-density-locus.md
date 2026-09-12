---
rg: 2
id: tracial-comparison-gives-gamma-on-lfnd-rank-density-locus
kind: claim
title: Projection comparison in the tracial ultrapower forces uniform Gamma for nuclear algebras with tracially locally finite nuclear dimension and bounded rank density
distinct_from:
  tracial-projection-comparison-forces-uniform-gamma: that is the same implication for every nuclear algebra; this restricts to tracially locally finite nuclear dimension and bounded rank density, where it reduces to a single-element existence statement.
  comparison-forces-tracial-support-projections: that concludes vanishing support gaps; this concludes uniform Gamma, and the two are equivalent on this locus through established claims.
  stw99-xviii-holds-on-rr0-lfnd-locus: that assumes real rank zero of the algebra and strict comparison and concludes Z-stability; this assumes only comparison of projections in the tracial ultrapower plus bounded rank density and concludes uniform Gamma.
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with `T(A) ≠ ∅`. Suppose `A` has these three properties:
- tracially locally finite nuclear dimension;
- bounded rank density;
- comparison of projections by limit traces in every `M_k(A^U)`.

Then `A` has uniform property Gamma.

**Consequences.**
- With `strict-comparison-compares-ultrapower-projections` and
  `uniform-gamma-algebras-satisfy-toms-winter`, this gives the unital
  Toms--Winter conjecture for such algebras.
  - That is new only for algebras whose nuclear dimension is locally finite
    tracially but not in norm.
  - With norm locally finite nuclear dimension and rank density, strict
    comparison already gives Z-stability through
    `rank-density-and-strict-comparison-give-purity` and Winter's theorem.
  - The hypothesis here is weaker than strict comparison, so the implication
    itself is open on the whole locus.
- Its failure is exactly a witness to `gamma-failure-invisible-to-projection-comparison`
  on this locus.

## Attempts

- **Reduction.** Route `lfnd-locus-gamma-via-support-projections` reduces this
  claim to `comparison-forces-tracial-support-projections`.
  - Comparison plus bounded rank density divides projections.
  - Support projections plus division give Gamma under the dimension hypothesis.
  - The attacks on the single-element statement are recorded there. None goes
    beyond it.

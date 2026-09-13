---
rg: 2
id: toms-winter-holds-on-tlfnd-rank-density-locus
kind: claim
title: Strict comparison forces Z-stability for unital simple separable nuclear algebras with tracially locally finite nuclear dimension and bounded rank density
distinct_from:
  stw99-problem-xviii-toms-winter-conjecture: that is the full conjecture with no locus restriction; this proves the open direction on algebras with tracially locally finite nuclear dimension and bounded rank density.
  stw99-xviii-holds-on-rr0-lfnd-locus: that assumes real rank zero and norm locally finite nuclear dimension; this assumes tracially locally finite nuclear dimension and near-projection rank density at bounded matrix size, with no real rank hypothesis.
  tracial-comparison-gives-gamma-on-lfnd-rank-density-locus: that assumes only projection comparison in the tracial ultrapower and is open; this assumes strict comparison of the algebra and concludes Z-stability.
  uniform-gamma-algebras-satisfy-toms-winter: that assumes uniform property Gamma; this derives uniform Gamma on the locus from strict comparison and then applies that claim.
artifacts:
  - research/artifacts/tw-support-gap-crux-2026-09-12.md
---

**Theorem.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with `T(A) ≠ ∅`. Suppose `A` has:
- tracially locally finite nuclear dimension (Vaccaro, arXiv:2604.24682,
  Definition 1.5);
- bounded rank density (RD_b, as in
  `ultrapower-comparison-with-rank-density-divides-projections`).

If `A` has strict comparison of positive elements, then `A` is Z-stable and has
finite nuclear dimension.

**Proof** (Section 2 of the artifact). Each step is an established claim.
1. Strict comparison gives projection comparison in every `M_k(A^U)`
   (`strict-comparison-compares-ultrapower-projections`).
2. Comparison and RD_b divide every projection
   (`ultrapower-comparison-with-rank-density-divides-projections`).
3. Strict comparison and RD_b make every support gap vanish
   (`strict-comparison-with-rank-density-gives-support-projections`).
4. Support projections plus division give uniform Gamma under tracially
   locally finite nuclear dimension
   (`uniform-gamma-iff-tracial-support-projections-and-division`).
5. Uniform Gamma and strict comparison give Z-stability
   (`uniform-gamma-algebras-satisfy-toms-winter`, CETW Theorem A).

**Scope.**
- With norm locally finite nuclear dimension this was already known, through
  `rank-density-and-strict-comparison-give-purity` and Winter's theorem. The new
  part is tracially-but-not-norm locally finite nuclear dimension.
- So a Toms–Winter counterexample must fail RD_b or fail tracially locally
  finite nuclear dimension.
- **Nearby known result.** Lin (`strict-comparison-rank-surjectivity-forces-sr1`),
  Vaccaro Theorem B and CETW together give the same conclusion when the rank
  map is surjective. How RD_b relates to surjectivity was not checked, and no
  novelty is asserted.

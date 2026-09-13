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
  `rank-density-and-strict-comparison-give-purity` and Winter's theorem. The
  tracially-but-not-norm case is new to the graph, but it is also a corollary of
  known results (last bullet).
- So a Toms–Winter counterexample must fail RD_b or fail tracially locally
  finite nuclear dimension.
- **Known results give the same conclusion** (review
  `research/artifacts/review-swarm4-2026-09-12.md`, Section 40). RD_b and strict
  comparison make the rank map `Gamma` of
  `strict-comparison-rank-surjectivity-forces-sr1` surjective:
  1. By Edwards, a lower semicontinuous affine `f: T(A) -> (0, infinity]` is
     `sup_n f_n` with continuous affine `0 < f_1 < f_2 < ...`.
  2. RD_b gives positive contractions `q_n ∈ M_(k_n)(A)`, with `k_n >= max f_n`,
     of profile `f_n` within `η_n` and defect below `η_n`. Since `|d_τ((q − 1/2)_+) − τ(q)| ≤ 2τ(q − q²)`, the rank
     of `x_n = (q_n − 1/2)_+` is within `3η_n` of `f_n`.
  3. Choose `η_n` decreasing to `0` with `6η_n < min_τ (f_{n+1} − f_n)`. Then
     `d_τ(x_n) < d_τ(x_{n+1})` for all `τ`, strict comparison makes the `x_n`
     Cuntz increasing, and their supremum in `Cu(A)` has rank `f`.

  So Lin gives stable rank one. Vaccaro (arXiv:2604.24682: stable rank one and
  tracially locally finite nuclear dimension give uniform property Gamma) gives
  uniform Gamma, and CETW Theorem A gives Z-stability. The route above is an
  independent derivation of the same conclusion, and no novelty is asserted.

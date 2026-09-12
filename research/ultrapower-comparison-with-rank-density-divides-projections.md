---
rg: 2
id: ultrapower-comparison-with-rank-density-divides-projections
kind: claim
title: Projection comparison in the tracial ultrapower with bounded rank density divides every projection of the ultrapower
distinct_from:
  strict-comparison-compares-ultrapower-projections: that derives comparison of ultrapower projections from strict comparison of the algebra; this assumes that comparison, adds rank density in bounded matrix size, and concludes that every projection of every matrix amplification of the ultrapower carries a unital copy of every matrix algebra.
  rank-density-and-strict-comparison-give-purity: that gives almost divisibility of the Cuntz semigroup of the algebra from rank density and strict comparison of positive elements; this gives exact division of projections in the tracial ultrapower from bounded rank density and comparison of ultrapower projections only.
  stw27-real-rank-zero-almost-divisibility: that divides compact Cuntz classes of a real rank zero algebra through large matrix blocks in projection corners; this divides projections of the tracial ultrapower with no real rank hypothesis, using comparison by limit traces and near projections of prescribed profile.
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

Let `A` be a unital, simple, separable, non-elementary C*-algebra with
`T(A) ≠ ∅`, and let `A^U` be its uniform tracial ultrapower. Suppose:

- **(PC)** for every `k`, projections `p, q ∈ M_k(A^U)` with `σ(p) ≤ σ(q)` for all
  limit traces satisfy `p ≾ q`;
- **(RD_b) bounded rank density** for every `k`, every continuous affine
  `f: T(A) → [0,k]` and every `η > 0`, there is a positive contraction
  `b ∈ M_k(A)` with `sup_τ |τ(b) − f(τ)| < η` and `sup_τ τ(b − b²) < η`.

Then for all `k, n`, every projection `p ∈ M_k(A^U)` admits a unital
*-homomorphism `M_n → p M_k(A^U) p`.

**Proof.**
1. RD_b applied stagewise to `τ ↦ τ(p_m)/n` gives a projection `e'` with
   `σ(e') = σ(p)/n`.
2. Comparison places `n − 1` orthogonal copies of `e'` under `p`.
3. The remainder has the profile of `e'`. Comparison and the vanishing of
   positive elements with all limit traces zero make it equivalent to `e'`.
4. The partial isometries give matrix units.

This is Section 3 of the artifact, and it is the corner form of Section 4.1 of
`research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`.
There strict comparison and the unit were used. Here PC replaces strict
comparison, and the matrix size is held fixed.

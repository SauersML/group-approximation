---
rg: 2
id: strict-comparison-with-rank-density-gives-support-projections
kind: claim
title: Strict comparison with bounded rank density gives near projections under every positive contraction with trace at least its trace
distinct_from:
  comparison-forces-tracial-support-projections: that assumes only projection comparison in the tracial ultrapower plus tracially locally finite nuclear dimension and is open; this assumes strict comparison of positive elements of the algebra and uses no dimension, nuclearity or Gamma hypothesis.
  strict-comparison-compares-ultrapower-projections: that compares projections that already exist in the tracial ultrapower; this produces projections inside the hereditary subalgebra of a single positive contraction.
  rank-density-and-strict-comparison-give-purity: that gives almost divisibility of the Cuntz semigroup from rank approximants in M_infty(A) and strict comparison; this gives near projections under one element with trace at least its trace, from near-projection profile selection at bounded matrix size.
  uniform-gamma-iff-tracial-support-projections-and-division: that shows vanishing support gaps necessary for uniform Gamma and, with projection division, sufficient under tracially locally finite nuclear dimension; this proves vanishing support gaps from strict comparison and bounded rank density, with no Gamma hypothesis.
artifacts:
  - research/artifacts/tw-support-gap-crux-2026-09-12.md
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

**Theorem.** Let `A` be a unital simple C*-algebra with `T(A) ≠ ∅`. Suppose:
- **Strict comparison.** For all `m` and `x, y ∈ M_m(A)_+`, `d_τ(x) < d_τ(y)` for
  every `τ ∈ T(A)` implies `x ≾ y`.
- **(RD_b) bounded rank density.** For every `k`, every continuous affine
  `f: T(A) → [0,k]` and every `η > 0`, there is a positive contraction
  `q ∈ M_k(A)` with `sup_τ |τ(q) − f(τ)| < η` and `sup_τ τ(q − q²) < η`.

Then `γ_A(a) = 0` for every `k` and every positive contraction `a ∈ M_k(A)`. That
is, for every `ε > 0` there is a positive contraction `b ∈ closure(a M_k(A) a)`
with `sup_τ τ(b − b²) < ε` and `sup_τ (τ(a) − τ(b)) < ε`. Equivalently, `A` has
tracial support projections.

**Proof sketch.**
1. RD_b gives a near projection `q` with profile `(1 − ε)τ(a)`.
2. The spectral estimates give `d_τ((q − δ)_+) < τ(a) ≤ d_τ(a)` for all `τ`,
   using that traces are faithful and `T(A)` is compact.
3. Strict comparison and Rørdam's lemma give `c_0` with `c_0c_0* = (q − 2δ)_+`
   and `c_0*c_0 ∈ closure(a M_k(A) a)`.
4. `b = ψ(c_0*c_0)` is the near projection. It has the trace and defect of
   `φ(q)`, since `τ(h(c*c)) = τ(h(cc*))` whenever `h(0) = 0`.

The full proof is Section 1 of the artifact.

**Consequence.** Under tracially locally finite nuclear dimension and RD_b,
strict comparison gives uniform property Gamma, hence Z-stability
(`toms-winter-holds-on-tlfnd-rank-density-locus`). A support-gap certificate
against Gamma never coexists with strict comparison and RD_b.

No novelty is asserted.

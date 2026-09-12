---
rg: 2
id: uniform-gamma-iff-tracial-support-projections-and-division
kind: claim
title: Uniform property Gamma forces tracial support projections and projection division, and the two give Gamma under tracially locally finite nuclear dimension
distinct_from:
  stw99-problem-xxi-tracial-rr0-implies-gamma: that asks whether real rank zero of the tracial ultrapower gives Gamma with no dimension hypothesis; this proves Gamma from two weaker ultrapower properties under tracially locally finite nuclear dimension. The two properties are projections under one positive contraction with trace at least its trace, and division of projections that already exist.
  stw99-problem-xxviii-tracial-divisibility-gamma: that asks whether Winter's order zero tracial divisibility gives Gamma with no dimension control; this derives that divisibility from support projections plus division, then spends the dimension hypothesis, and proves both properties necessary for Gamma in every nuclear algebra.
  rank-density-is-quadratic-trace-selection: that characterizes approximate ranks by near projections of prescribed trace profile anywhere in the algebra; this uses near projections inside the hereditary subalgebra of one positive contraction, with trace at least that of the contraction.
  strict-comparison-compares-ultrapower-projections: that proves Murray--von Neumann comparison of existing ultrapower projections from strict comparison; this concerns existence of projections under single elements and division of projections, which comparison alone does not supply.
  stw99-xviii-holds-on-rr0-lfnd-locus: that proves Toms--Winter for real rank zero algebras with locally finite nuclear dimension through almost divisibility of the Cuntz semigroup; this is a tracial-ultrapower criterion for uniform Gamma with no real rank or comparison hypothesis on the algebra.
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

**Setting.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with `T(A) ≠ ∅`, and let `A^U` be its uniform tracial ultrapower. For
a positive contraction `a ∈ M_k(A)`, write `her(a)^U` for the image of
`ℓ^∞(closure(a M_k(A) a))` in `M_k(A^U)`, and put

```text
γ_A(a) = inf over positive contractions b ∈ closure(a M_k(A) a) of
         max{ sup_τ τ(b − b²),  sup_τ (τ(a) − τ(b)) }.
```

- **(TSP) Tracial support projections.** For every `k`, `a` and `ε > 0` there is a
  projection `p ∈ her(a)^U` with `σ(p) ≥ σ(a) − ε` for every limit trace. This
  holds for `a` if and only if `γ_A(a) = 0`.
- **(PD) Projection division.** For all `k, n`, every projection `p ∈ M_k(A^U)`
  admits a unital *-homomorphism `M_n → p M_k(A^U) p`.

**Theorem.**
- (a) If `A` has uniform property Gamma, then `γ_A(a) = 0` for every `a`, and PD
  holds.
- (b) If `A` has tracially locally finite nuclear dimension, then TSP and PD
  together give uniform property Gamma.

So a single positive contraction `a` with `γ_A(a) > 0` certifies failure of
uniform Gamma in any such algebra.
- **Not a comparison certificate.** It is an existence gap under one element,
  not a pair of non-subequivalent projections. So
  `strict-comparison-bundle-certificate-vanishes` does not rule it out.
- **The same criterion.** Under tracially locally finite nuclear dimension,
  uniform Gamma is equivalent to "single-element McDuff": a unital
  `M_N ⊂ M_k(A^U)` commuting with any prescribed `a`.

**Proof outline.**
- **(a)** CETW Theorem 4.6 gives unital `M_N → A^U ∩ A'`.
  - A Lebesgue-distributed central `h` gives the near projection
    `g_δ(a − (η + (1−η)h))`. It lies in `her(a)^U`, has defect at most `ε` and
    trace at least `τ(a) − ε`.
  - Reindexing against a given projection gives PD.
- **(b)** TSP gives `p` under `a`, and PD divides `p`.
  - Order zero lifting gives Vaccaro's tracial almost divisibility
    (Definition 1.3).
  - Vaccaro's Proposition 1.6, (2)⇒(1), then makes `A` uniformly McDuff, and
    CETW Theorem 4.6 gives uniform Gamma.

Full proofs: Sections 1–2 of the artifact.

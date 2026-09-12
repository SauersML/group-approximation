---
rg: 2
id: strict-comparison-bundle-certificate-vanishes
kind: claim
title: Under strict comparison, equal-trace projections of the uniform tracial completion are approximately equivalent
distinct_from:
  strict-comparison-compares-ultrapower-projections: that gives Murray--von Neumann subequivalence in the tracial ultrapower from dominated limit traces; this derives two-sided approximate equivalence by contractions inside the completion from equal traces, which is the form the bundle certificate uses.
  trivial-r-fibre-bundles-compare-equal-trace-projections: that proves the same approximate equivalence in the trivial bundle C_σ(K,R) with no comparison hypothesis; this proves it in the completion of every exact algebra with strict comparison, trivial or not, so the certificate built on that claim is blind there.
  gamma-failure-invisible-to-projection-comparison: that is the open existence of an algebra lacking uniform Gamma whose ultrapower compares projections; this is the proved statement that strict comparison already makes every equal-trace pair in the completion approximately equivalent.
  toms-gamma-counterexample-fails-strict-comparison: that excludes strict comparison for AH algebras without uniform Gamma through ranks and purity; this excludes it for every exact algebra carrying an equal-trace pair that is not approximately equivalent, whatever its building blocks.
artifacts:
  - research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md
---

Let `A` be a unital, simple, separable, exact, non-elementary C*-algebra with
`T(A) ≠ ∅` and strict comparison. Let `M` be its uniform tracial completion, and
let `P, Q ∈ M_k(M)` be projections with `τ(P) = τ(Q)` for every `τ ∈ T(A)`. Then
for every `ε > 0` there is a contraction `W ∈ M_k(M)` with

```text
W = QWP,     ‖W*W − P‖_{2,u} ≤ ε,     ‖WW* − Q‖_{2,u} ≤ ε.
```

**The two requirements are incompatible.** Suppose an algebra has equal-trace
projections in its completion that are not approximately equivalent. Then it
fails strict comparison, whatever its connecting maps, building blocks or trace
simplex. In particular, if `T(A)` is Bauer and `A` has strict comparison, the
nontriviality criterion of `trivial-r-fibre-bundles-compare-equal-trace-projections`
never applies to its bundle.

A Toms–Winter counterexample with a Bauer simplex would still give a nontrivial
bundle, by `bauer-uniform-gamma-iff-trivial-tracial-bundle` and
`uniform-gamma-algebras-satisfy-toms-winter`, but this certificate cannot detect
it. The bundle question `nontrivial-w-star-bundle-with-r-fibres-exists` has no
comparison hypothesis, and it stays open.

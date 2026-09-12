---
rg: 2
id: r-fibre-w-star-bundle-finite-dim-base-is-trivial
kind: claim
title: A strictly separable W*-bundle with hyperfinite II_1 fibres over a finite-dimensional base is trivial
distinct_from:
  r-fibre-w-star-bundle-locally-trivial-is-trivial: that assumes local triviality and allows any base; this assumes nothing about local structure but needs finite covering dimension.
  uniform-gamma-on-finite-dim-boundaries: that is the C*-algebra statement that a compact finite-dimensional tracial boundary forces uniform Gamma; this is Ozawa's bundle theorem, which applies to arbitrary strictly separable bundles and to their restrictions to closed subsets.
  stw22-finite-dimensional-trivial-field-traces: that proves trace continuity for trivial UHF fields over finite-dimensional bases; this is triviality of the bundle itself.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

Let `M` be a strictly separable continuous W*-bundle over a compact space `K` of
finite covering dimension, with every fibre isomorphic to `R`.  Then
`M ≅ C_σ(K,R)`.

The same paper characterizes triviality of an `R`-fibre bundle over any `K`
(Theorem 15) by the existence of approximately central approximate projections
of conditional expectation `1/2`, in the uniform 2-norm.  Ozawa remarks that it
is unclear whether finite dimensionality is essential; that is BBSTWW Question
3.14 (`nontrivial-w-star-bundle-with-r-fibres-exists`).

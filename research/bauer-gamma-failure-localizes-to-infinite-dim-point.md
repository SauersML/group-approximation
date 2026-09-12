---
rg: 2
id: bauer-gamma-failure-localizes-to-infinite-dim-point
kind: claim
title: A nontrivial hyperfinite W*-bundle fails local triviality only at points of infinite local dimension
distinct_from:
  r-fibre-w-star-bundle-finite-dim-base-is-trivial: that assumes the whole base is finite-dimensional; this localizes nontriviality to the closed set of points every neighbourhood of which is infinite-dimensional, for any compact metrizable base.
  r-fibre-w-star-bundle-locally-trivial-is-trivial: that is the local-to-global theorem; this combines it with Ozawa's theorem on restrictions to say where local triviality can fail.
  gamma-failure-invisible-to-projection-comparison: that asks for a nuclear algebra without uniform Gamma whose tracial ultrapower compares projections; this constrains the extreme boundary of every such algebra with a Bauer trace simplex.
  uniform-gamma-on-finite-dim-boundaries: that proves uniform Gamma for compact finite-dimensional extreme boundaries; this shows Gamma failure on a Bauer simplex is confined to the points where the boundary is locally infinite-dimensional.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

Let `M` be a strictly separable continuous W*-bundle over a compact metrizable
space `K` with every fibre isomorphic to `R`.  Put

```text
Z(M)  = { x : no closed neighbourhood Y of x has M_Y trivial },
K_inf = { x : no closed neighbourhood of x has finite covering dimension }.
```

Then `Z(M)` and `K_inf` are closed, `M` is trivial if and only if `Z(M)` is
empty, and `Z(M) ⊆ K_inf`.  Moreover `K_inf` is empty exactly when
`dim K < ∞`.

**Algebra form.**  Let `A` be unital, simple, separable, nuclear and
non-elementary with `T(A)` Bauer, and suppose `A` lacks uniform property Gamma.
Then some extreme trace `τ_0` has the following property.  For every closed
neighbourhood `Y` of `τ_0` in `∂_e T(A)`, the restricted strict closure `M_Y`
admits no sequence of approximately central approximate projections with
conditional expectation tending to `1/2`, and `Y` has infinite covering
dimension.

In particular every unital Toms--Winter counterexample with a Bauer trace simplex
has such an extreme trace, and its strict closure is a nontrivial `R`-fibre
bundle (`nontrivial-w-star-bundle-with-r-fibres-exists`).  This sharpens
Mommaerts's Remark 4.7 (arXiv:2606.12134), which asks only that the base be
infinite-dimensional.  For example, over the one-point compactification of
the disjoint union of the cubes `[0,1]^n`, a nontrivial bundle is trivial over
each cube and fails local triviality only at the added point.

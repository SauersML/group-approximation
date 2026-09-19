---
rg: 2
id: stw81-finite-base-usc-fibre-product-bound
kind: claim
title: Arbitrary upper-semicontinuous fields obey the base-times-fibre nuclear-dimension bound
distinct_from:
  stw81-zero-dimensional-usc-fibre-formula: that theorem gives exact equality over a zero-dimensional base; the present theorem allows every finite-dimensional base and pays one independent topological colour coordinate.
  stw81-af-fibre-fields-have-base-bound: that theorem treats arbitrary finite-dimensional bases but requires AF fibres; the present theorem allows uniformly finite positive fibre dimension.
artifacts:
  - research/artifacts/stw81-finite-base-usc-product-audit-2026-08-30.md
---

Let `X` be a second-countable locally compact Hausdorff space with
`dim(X)=n<infinity`, and let `A` be a separable `C_0(X)`-algebra.  No
continuity-field or local-triviality hypothesis is imposed.  If

```text
d=sup_(x in X) dim_nuc(A_x)<infinity,
```

then

```text
d <= dim_nuc(A) <= (n+1)(d+1)-1.                       (FBP1)
```

The upper bound is obtained without locally lifting incoming maps.  At each
anchor, the `d+1` outgoing fibre colours lift exactly through evaluation by
projectivity of finite-dimensional cones.  Upper semicontinuity gives a
neighborhood on which the lifted approximation and the sum of its colour
units are controlled.  An `(n+1)`-decomposable refinement of the base cover
then produces the independent colour pairs

```text
(base colour, fibre colour).
```

Central cutoffs make equal base colours orthogonal.  Each paired colour is
c.p.c. order zero; nuclear dimension does not require their total sum to be
contractive.

If every nonzero fibre is simple, then the spectrum of every commutative
hereditary subalgebra in every quotient is locally homeomorphic to a
subspace of `X`, and hence has covering dimension at most `n`.  In
particular, for `n<=1` these fields satisfy the hereditary-shadow hypothesis
in STW Problem LXXXI.  Formula `(FBP1)` supplies a finite nuclear-dimension
bound whenever the fibre dimensions are uniformly finite, though it does
not by itself force the `0,1,infinity` trichotomy when `n=1`.

---
rg: 2
id: stw81-continuous-trace-rank-one-localization-proof
kind: route
title: Detect continuous-trace spectrum dimension in local rank-one corners
target: stw81-continuous-trace-positive
requires:
  - winter-zacharias-continuous-trace-nuclear-dimension
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Write `X=Prim(A)`.  This is a second-countable locally compact Hausdorff
space.  Fix `x in X`.  Local triviality of the compact-operator bundle of a
continuous-trace algebra gives an open neighborhood `U` of `x` over which
the restricted algebra is

```text
A(U) ~= C_0(U,K(H)).
```

Here the Hilbert space `H` may be finite- or infinite-dimensional.  Choose a
rank-one projection `e in K(H)`.  The corner

```text
C_0(U)e ~= C_0(U)
```

is a commutative hereditary subalgebra of the ideal `A(U)` and hence of
`A`.  The hypothesis gives `dim(U)<=1`.

Every point of `X` has such an open neighborhood.  Covering dimension is
local on second-countable locally compact Hausdorff spaces, so `dim(X)<=1`.
The Winter--Zacharias continuous-trace computation now gives

```text
dim_nuc(A)=dim(X)<=1.
```

The argument does not require a global rank-one projection or a trivial
Dixmier--Douady class: all dimension detection is local.

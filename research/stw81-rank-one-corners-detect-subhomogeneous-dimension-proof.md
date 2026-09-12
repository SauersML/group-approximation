---
rg: 2
id: stw81-rank-one-corners-detect-subhomogeneous-dimension-proof
kind: route
title: Detect every homogeneous stratum dimension in a local rank-one corner
target: stw81-separable-subhomogeneous-positive
requires: []
---

A separable subhomogeneous algebra has a finite composition series whose
successive subquotients are homogeneous.  Fix one such subquotient `D`, say
`k`-homogeneous with locally compact second-countable Hausdorff spectrum
`X`.

Every point of `X` has an open neighborhood `U` over which the matrix bundle
of `D` is trivial.  Passing to the ideal that restricts the bundle to `U`
and cutting by a constant rank-one matrix projection gives a hereditary
subalgebra

```text
C ~= C_0(U).
```

This `C` is a commutative hereditary subalgebra of an ideal in the
subquotient `D`.  Ideals of an ideal are ideals of the ambient C-star
algebra, so `C` is also a commutative hereditary subalgebra of a quotient of
`A`, exactly of the kind quantified over in Problem LXXXI.  The hypothesis
therefore gives

```text
dim(U)=dim(Prim(C)) <= 1.
```

Covering dimension is local on second-countable locally compact Hausdorff
spaces.  Since every point of `X` has such a neighborhood, `dim(X)<=1`.
This applies to every homogeneous subquotient in the finite composition
series.

For separable subhomogeneous algebras, nuclear dimension is the maximum of
the covering dimensions of these homogeneous strata.  Hence

```text
dim_nuc(A) <= 1,
```

as claimed.  Notice that the proof uses the full hereditary-quotient
hypothesis: looking only at commutative subalgebras of `A` itself would not
automatically expose every local rank-one corner of every stratum.

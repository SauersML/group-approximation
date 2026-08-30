---
rg: 2
id: stw82-one-dimensional-middle-forces-maximum
kind: claim
title: Every extension inside a separable nuclear-dimension-one algebra obeys the maximum formula
distinct_from:
  stw82-subhomogeneous-maximum: that computes arbitrary-dimensional extensions from subhomogeneity of the two endpoints; this theorem assumes only a two-colour ceiling on the middle algebra and applies to every ideal in that algebra.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that characterizes a particular projectional gluing mechanism; this theorem requires no quasidiagonality and uses rigidity at nuclear dimensions zero and one.
---

Let

```text
0 -> I -> E -> D -> 0
```

be an extension of separable C*-algebras.  If

```text
dim_nuc(E) <= 1,
```

then

```text
dim_nuc(E)=max(dim_nuc(I),dim_nuc(D)).                 (M1)
```

Equivalently, every ideal--quotient decomposition of a separable algebra of
nuclear dimension at most one satisfies the desired extension formula.  In
particular, a counterexample to STW Problem LXXXII must have middle nuclear
dimension at least two.  There is no hidden `+1` in (M1).

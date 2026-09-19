---
rg: 2
id: stw99-lxvi-full-finite-corner-is-nonstable-proof
kind: route
title: Pull an infinite ambient projection into a matrix over the finite full corner
target: stw99-lxvi-maximal-finite-corner-criterion
requires:
  - stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain
---

Put `A=pBp`.  A nonzero hereditary corner of a simple algebra is simple, and
its unit is `p`.  Thus `A` is simple and unital, and `1_A` is finite.  The
coherent dyadic chain gives a unital CAR embedding by
`stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain`.

It remains to prove that `A` is not stably finite.  Let `r` be an infinite
projection in `B`.  Since `p` is nonzero and `B` is simple, `p` is full.
Compactness of the projection class `[r]` then gives a finite `m` with

```text
[r] <= m[p].
```

Projection comparison realizes a projection `r'<=p directSum ... directSum p`
in `M_m(B)` which is Murray--von Neumann equivalent to `r`.  Hence `r'` is
infinite and belongs to `M_m(pBp)=M_m(A)`.

An infinite subprojection makes the containing unit infinite: if
`v*v=r'` and `vv*<r'`, then

```text
w = v + (1_(M_m(A))-r')
```

is an isometry with proper range in `M_m(A)`.  Thus a matrix amplification of
`A` has infinite unit, so `A` is not stably finite.

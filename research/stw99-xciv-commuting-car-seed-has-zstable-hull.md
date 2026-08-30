---
rg: 2
id: stw99-xciv-commuting-car-seed-has-zstable-hull
kind: claim
title: A separable seed with a commuting CAR copy has a Z-stable hull
distinct_from:
  stw99-problem-xciv-hyperfinite-factor-separably-z-stable: that asks for a hull for every norm-separable subset of R; this theorem applies when the exact relative commutant of the chosen seed contains a unital CAR algebra.
---

Let `B` be a unital C\*-algebra, let `S subset B` be norm separable, and put

```text
A=C*(S,1_B).
```

If `A' intersect B` contains a unital copy `U` of the CAR algebra, then
`S` is contained in a separable unital `Z`-stable C\*-subalgebra of `B`.
More precisely, multiplication induces an isomorphism

```text
A tensor_min U  ~=  C*(A,U) subset B.
```

Consequently this criterion applies to every norm-separable subset of one
tensor leg in a decomposition `R=R_0 bar_tensor R_1`: put a CAR copy in the
other leg.  This is a genuinely infinite-dimensional positive class for
Problem XCIV; for example the subset in the first leg may generate a diffuse
abelian algebra or another CAR algebra.


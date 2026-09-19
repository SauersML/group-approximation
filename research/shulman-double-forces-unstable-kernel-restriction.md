---
rg: 2
id: shulman-double-forces-unstable-kernel-restriction
kind: claim
title: The weak-MF presentation double forces dimension-uniform failure of restriction stability
distinct_from:
  symmetric-double-weak-mf: that proves operator-norm MF for every symmetric double of a residually finite group; this extracts the resulting pair of exact vertex representations for a presentation kernel.
  simple-map-quotient-has-rigid-fd-restriction: that proves exact injectivity in every fixed dimension; this proves the inverse restriction maps have no dimension-uniform pointwise operator-norm modulus.
  dimension-defect-controlled-mf-hyperlinear: that converts an MF sequence with a strong dimension-defect rate into hyperlinear microstates; this identifies a restriction-instability sequence but supplies no such rate or positive normalized rank.
---

**ESTABLISHED.** Let `F` be a finitely generated free group, `K normal F`,
and choose `f_0 in F\K`. Then there are exact finite-dimensional
representations

```text
u_n,v_n:F->U(d_n)                                         (PRI1)
```

and `c>0` such that

```text
||u_n(k)-v_n(k)||_op -> 0       for every fixed k in K,   (PRI2)
||u_n(f_0)-v_n(f_0)||_op >= c   along a tail.             (PRI3)
```

The double `P=F *_K F` is weak/operator-MF by
`symmetric-double-weak-mf`. Lift the images of the free generators in its two
vertex groups from an injective norm-corona representation. Freeness turns
those lifts into the exact homomorphisms `(PRI1)`. The amalgam relations give
`(PRI2)` after diagonalizing over an exhaustion of `K`. The reduced word
`i_0(f_0)i_1(f_0)^(-1)` is nontrivial by the amalgam normal-form theorem, so
norm-corona injectivity gives `(PRI3)` on a subsequence.

When `F/K` is simple and nonsofic, `(PRI1)--(PRI3)` coexist with the exact
injectivity theorem `simple-map-quotient-has-rigid-fd-restriction`. Hence the
inverse restriction maps are injective in every dimension but admit no
dimension-uniform pointwise operator-norm modulus.

DERIVATION
shulman-kernel-restriction-instability-proof

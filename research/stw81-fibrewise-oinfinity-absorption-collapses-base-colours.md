---
rg: 2
id: stw81-fibrewise-oinfinity-absorption-collapses-base-colours
kind: claim
title: Fibrewise O-infinity absorption collapses all base colours without field continuity
distinct_from:
  stw81-one-dim-elementary-oinfty-fields-have-dim-one: that theorem assumes a locally trivial field in order to split its elementary and O-infinity loci; the present pure absorbing theorem needs neither local triviality nor continuity, and its mixed version assumes only the exact clopen continuous-trace split used in the conclusion.
  stw81-finite-base-usc-fibre-product-bound: that theorem multiplies base and fibre colours and gives three over a one-dimensional base with dimension-one fibres; absorption here collapses the global algebra to nuclear dimension at most one.
  stw81-oinfinity-envelopes-have-dimension-one-or-infinity: that theorem assumes a displayed global tensor-product envelope; the present theorem detects global absorption solely from the fibres of an arbitrary upper-semicontinuous field.
artifacts:
  - research/artifacts/stw81-fibrewise-oinfinity-colour-collapse-audit-2026-08-30.md
---

Let `X` be a finite-dimensional second-countable locally compact Hausdorff
space, and let `A` be a separable nuclear `C_0(X)`-algebra.  No continuity
or local-triviality hypothesis is imposed.  If every fibre satisfies

```text
A_x tensor O_infinity isomorphic to A_x,
```

then

```text
A tensor O_infinity isomorphic to A,
dim_nuc(A)<=1.                                           (FOC1)
```

If `A` is nonzero and its nonzero fibres are simple, then
`dim_nuc(A)=1`, and no quotient of `A` contains a nonzero commutative
hereditary C-star subalgebra.  In particular, over a base of dimension at
most one this is an upper-semicontinuous, non-locally-trivial positive class
for STW Problem LXXXI.

There is also a mixed version requiring no local triviality.  Suppose
`dim(X)<=1`, the fibres of `A` are simple, and

```text
X=X_el disjoint_union X_inf
```

is a clopen decomposition such that the restriction to `X_el` is a
continuous-trace algebra with spectrum `X_el`, while every fibre over
`X_inf` is O-infinity-stable.  Then

```text
dim_nuc(A)<=1,                                           (FOC2)
```

and every commutative hereditary subalgebra in every quotient has spectrum
of covering dimension at most one.  Thus the local-triviality hypothesis in
the earlier elementary/O-infinity field theorem can be replaced by exactly
the clopen continuous-trace structure on the elementary part; the absorbing
part remains an arbitrary upper-semicontinuous field.

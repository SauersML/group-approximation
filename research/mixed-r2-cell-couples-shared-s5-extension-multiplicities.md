---
rg: 2
id: mixed-r2-cell-couples-shared-s5-extension-multiplicities
kind: claim
title: One mixed R2 cell couples the two S6 extension multiplicity spaces
distinct_from:
  shared-s5-selector-face-has-multiplicity-rotation-gauge: that rotates two S6 extensions while preserving every relation internal to either extension and their whole common S5 face; this identifies a single cross-extension relation whose defect is exactly the missing-arm mismatch.
  shared-endpoint-r2-r3-anchor-has-linear-seam-bound: that assumes a common transported endpoint or a common split parent and child; this uses one input arm from one extension and the transported arm from the other extension in the same R2 triangle.
  finite-s6-selector-centralizer-pins-common-pivot-arm: that uses three commutators after a joint S6 exactification; this is an exact two-line cancellation and needs neither a selector gap nor representation theory.
---

Let

```text
Omega={i,p,j,k,l,q},
H=Sym({p,j,k,l,q}) < Sym(Omega),
x=(i p),             y=(i q),             r=(p q) in H.         (MRC1)
```

Suppose `rho_0,rho_1:Sym(Omega)->U(d)` are two unitary
representations with the same restriction to `H`.  Write

```text
X_a=rho_a(x),        Y_a=rho_a(y),        R=rho_0(r)=rho_1(r).
```

The within-chart R2 triangles are

```text
Y_a X_a Y_a=R.                                                (MRC2)
```

If one additionally retains the **mixed** R2 triangle, using the input arm
of chart zero and the transported arm of chart one, then

```text
||X_0-X_1||_2
 =||Y_1 X_0 Y_1-R||_2.                                      (MRC3)
```

More generally, for approximate involutions and an approximate chart-one
triangle,

```text
||X_0-X_1||_2
 <=||Y_1 X_0 Y_1-R||_2+||Y_1 X_1 Y_1-R||_2.                 (MRC4)
```

Thus one mixed R2 cell kills the entire finite-dimensional multiplicity
rotation from `shared-s5-selector-face-has-multiplicity-rotation-gauge`.
Indeed, for `rho_1=U rho_0 U^*` with `U in rho_0(H)'`, the mixed-cell
defect in `(MRC3)` is exactly

```text
||rho_0(x)-U rho_0(x)U^*||_2,                               (MRC5)
```

which is positive precisely when the rotation changes the missing arm.

This relation is native to the Bleak--Quick presentation.  At the normalized
depth-three labels

```text
p=000,       q=001,       i=010,
```

put `s=(010 000)`, `t=(010 001)`, and `r=(000 001)`.  The identity

```text
t s t=r                                                       (MRC6)
```

is a conjugate of R2,

```text
(1 01)^(1 00)=(00 01).
```

The remaining issue is not which finite relation detects the gauge: it is
whether one bounded Bleak--Quick diagram can retain the first occurrence of
`s` and the second occurrence of `t` in the *same* conjugate of R2.  Internal
R2 triangles in the two private charts do not do this.


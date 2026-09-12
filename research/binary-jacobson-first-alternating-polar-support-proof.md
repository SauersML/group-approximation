---
rg: 2
id: binary-jacobson-first-alternating-polar-support-proof
kind: route
title: Use the TS commutator to force the polar into one z-sign and compute its commuting-cut support
target: binary-jacobson-first-alternating-polar-is-half-supported
requires:
  - binary-jacobson-first-alternating-ts-closure-relation
  - binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple
---

The raw range `e=F_+` is obtained by conjugating the source cuts for
`x_13(Q),x_23(Q),x_13(ST)` by `a`.  The resulting same-position root cuts
include

```text
x_13(SQ)=-1,
x_13(S^2T)=+1.                                           (1)
```

Since `S^2T=S+SQ` in the additive Jacobson ring,

```text
x_13(S^2T)=x_13(S)x_13(SQ).                              (2)
```

Equations `(1)--(2)` imply `se=-e` for `s=x_13(S)`.

The alternating closure theorem gives the central Heisenberg relation

```text
u s u=z s,             u=x_21(T), z=x_23(1),             (3)
```

and `u` commutes with `z` because those two roots have the same source row.
Right multiplication of `A=eue` by the equality `se=-e` gives

```text
e u s e=-A.                                               (4)
```

Using `(3)` and again `se=-e`, the left side of `(4)` is

```text
e z s u e=-z e u e=-zA.                                  (5)
```

Thus `zA=A`.  Since `e,u` both commute with `z`, also `Az=A`, proving
`(JAP3)--(JAP4)`.

The word `X_0=x_12(Q)` commutes with every same-position root cut defining
`e`, hence preserves `e`.  The native Heisenberg relation gives

```text
X_0 z X_0=x_13(Q)z=-z                                    (6)
```

on `e`.  Therefore `X_0` exchanges the two `z` cuts in `e`, proving their
equal rank and nonvanishing.

Finally, conjugation by `u=x_21(T)` sends every root defining `e` to its
product with a root in position `(2,3)`.  All roots in positions `(1,3)`
and `(2,3)` commute (they share the target column).  Hence every defining
involution of `e` commutes with every defining involution of `ueu`, so the
two projections commute.  Since `u=u^*` and `e=e^*`,

```text
A^2=e u e u e=e(ueu)e=e(ueu).                            (7)
```

This is their intersection projection.  It can be read explicitly.  Put

```text
v=x_13(SQ),       d=x_13(S^2T),
Y=x_23(Q),        r=x_23(ST).                             (8)
```

On `e` one has `v=-1,d=+1`, and root commutators give

```text
u v u=Yv,         u d u=rd,        u x_13(Q)u=x_13(Q).   (9)
```

Thus membership in `ueu` additionally requires `Y=+1,r=+1`.  Since
`z=Yr`, either of these conditions implies the other on the already proved
`z=+1` support.  Therefore

```text
e meet (ueu)=e(1+z)(1+Y)/4.                              (10)
```

Equations `(JAP3)`, `(7)`, and `(10)` prove the exact support statement and
complete the fence.

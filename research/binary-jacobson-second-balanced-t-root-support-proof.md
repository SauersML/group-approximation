---
rg: 2
id: binary-jacobson-second-balanced-t-root-support-proof
kind: route
title: Conjugate the three raw head cuts by x_41(T) and read the two new x_43 signs
target: binary-jacobson-second-balanced-t-root-is-half-supported
requires:
  - binary-jacobson-balanced-center-fold-authenticates-two-rows
  - binary-jacobson-first-alternating-polar-is-half-supported
---

Write the three same-position root signs defining `e=F_+` as

```text
w=x_13(Q)=-1,       v=x_13(SQ)=-1,
d=x_13(S^2T)=+1.                                         (1)
```

The Steinberg relations for `l=x_41(T)` give

```text
lwl=w,
lvl=x_43(TSQ)v=x_43(Q)v,
ldl=x_43(TS^2T)d=x_43(ST)d.                              (2)
```

Here `TQ=0`, `TS=1`, and `TS^2=S`.  All original roots in position `(1,3)`
commute with the new roots in position `(4,3)`, and the two new roots commute
with one another.  Therefore `e` commutes with `lel`, and

```text
B^*B=e(lel)e=e meet (lel).                               (3)
```

On `e`, the extra requirements for membership in `lel` read
`x_43(Q)=+1` and `x_43(ST)=+1`, proving `(JST2)`.  The same calculation gives
`BB^*=p_l` because `B=B^*`.

Finally `X=x_14(Q)` commutes with every defining root of `e`, hence preserves
`e`, while

```text
X x_43(Q) X=x_13(Q)x_43(Q)=-x_43(Q)                     (4)
```

on `e`.  Thus `X` unitarily exchanges the positive and negative
`x_43(Q)` cuts inside `e`; each has half the rank of `e`.  Since `p_l` is a
subprojection of the positive cut, `(JST3)` follows.

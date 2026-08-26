---
rg: 2
id: binary-jacobson-balanced-center-fold-proof
kind: route
title: Fold two orthogonal center-related raw carriers and commute the Q-roots through the fold
target: binary-jacobson-balanced-center-fold-authenticates-two-rows
requires:
  - binary-jacobson-balanced-target-redesign-contains-mixed-root
  - binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple
---

The prerequisite proves

```text
e c_T e=0.                                                (1)
```

Since `c_T` is a self-adjoint involution, `e'=c_Tec_T` is a projection and

```text
ee'=e c_T e c_T=0.                                       (2)
```

Thus `E=e+e'` is a projection.  Conjugation by `c_T` exchanges `e,e'`, so
`E` commutes with `c_T` and `q=E(1-c_T)/2` is a projection.

Now `(1-c_T)^2=2(1-c_T)`.  Hence

```text
V^*V=e(1-c_T)e=e,
VV^*=(1-c_T)e(1-c_T)/2
    =(e+e')(1-c_T)/2=q,                                  (3)
```

where `(1)` is used in the first equality and direct expansion plus `(2)`
in the second.  This proves `(JCF2)`.

It remains to type the two exact rows.  Every defining cut of `e` lies in
root positions `(1,3)` or `(2,3)`.  The roots `x_12(Q)` and `x_14(Q)` commute
with those cuts, so they reduce `e`.  They are generators of the balanced
packet `D_T`, whose common center is `c_T`; therefore they also commute with
`c_T`.  For either `d=x_12(Q),x_14(Q)`,

```text
dV=d(1-c_T)e/sqrt(2)
  =(1-c_T)e d/sqrt(2)=V(d|_e).                            (4)
```

This is `(JCF3)`.  No assertion is made for `x_21(T)` or `x_41(T)`: those
roots do not reduce `e`, so moving them through the final factor `e` in
`(4)` would be exactly the missing covariance claim.

---
rg: 2
id: deleted-line-three-cycle-spectrum-proof
kind: route
title: Reduce the polar-compressed cubic to the cyclic span of the deleted line
target: deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
requires: []
---

Write `Y=XU`.  Since `Uq=q`, one has `Yq=Xq`.  Put

```text
beta=(1-a^2)^(1/2),       v=(Yq-aq)/beta.
```

In the orthonormal basis `(q,v)`, the restriction of `X` is

```text
[ a       beta ]
[ beta    -a   ].                                         (DLT1)
```

Moreover `A v=-a v`, while `A` is an involution on `v^perp` inside `PH`.
Thus the extension `Xhat=1_(Cq) (+) sgn(A)` equals `X` on
`span(q,v)^perp`, and, for `G=Xhat X`,

```text
Gq=2a q-Yq,             GYq=q.                         (DLT2)
```

The cyclic space

```text
K=span(q,Yq,Y^2q)
```

is `Y`-invariant.  Its three cyclic vectors have Gram matrix with diagonal
one and every off-diagonal entry `a`, because `Y^3=1` and `a` is real.
The operator `G` is the identity on `K^perp`.  In the cyclic basis
`e_0=q,e_1=Yq,e_2=Y^2q`, orthogonal projection of `e_2` onto
`span(e_0,e_1)` has both coefficients `a/(1+a)`.  Therefore

```text
G e_2=e_2+(2a^2/(1+a))e_0-(2a/(1+a))e_1.              (DLT3)
```

The matrix of `GY=Xhat U` in this basis is consequently

```text
[ 1   2a^2/(1+a)    2a ]
[ 0   -2a/(1+a)     -1 ]
[ 0       1           0 ].                             (DLT4)
```

It fixes `e_0`; on the quotient by `C e_0` its determinant is one and its
trace is `-2a/(1+a)`.  Hence its remaining eigenvalues are
`lambda,lambda^(-1)` with `(DFC3)`.  Cubing and using unitarity gives

```text
||(GY)^3-1||_F^2
 =4(1-cos(3 theta)),       cos(theta)=-a/(1+a)
 =4(1-a)^2(1+2a)/(1+a)^3.                              (DLT5)
```

Both `Xhat` and `U` fix `q`, so the restriction of `(Xhat U)^3` to `PH` is
exactly `(X_0U_0)^3`.  This proves the claim.  Finally, for `0<a<1/4`, use
`(1-a)^2>9/16`, `1+2a>1`, and `(1+a)^3<125/64` in `(DLT5)` to obtain
`144/125`.

---
rg: 2
id: authenticated-mixed-loop-minuscule-module-proof
kind: route
title: Compute the dual Fox rows and use extension closure
target: authenticated-mixed-loop-kills-minuscule-affine-modules
requires:
  - authenticated-mixed-loop-kills-natural-affine-gauges
---

Retain the coefficient abbreviations from
`authenticated-mixed-loop-natural-affine-proof` and set

```text
q=h x_21(-1)h^(-1)=x_21(-1/2),
s=h x_32(-1)h^(-1)=x_32(-1/2),
u=q x_13(1)q^(-1),                 r=x_23(-1),
A=x_12(2),                         B=d_12 x_23(2).       (MMP1)
```

For any representation `rho:F->GL(V)`, direct multiplication in
`V rtimes F` says that the translation parts of the torus and mixed words
are respectively

```text
rho(X)lambda,                    rho(Y)lambda,           (MMP2)
```

where `X,Y` are the following two elements of `KF`:

```text
X=A(1-q)+B(1-s)-1,
Y=(1-u)(1-q)-h^(-1)(r-1).                              (MMP3)
```

Thus the affine gauge space on `V` is exactly

```text
ker rho(X) intersect ker rho(Y).                        (MMP4)
```

The defining-module calculation already proves that `(MMP4)` is zero on
`M` and on every direct sum of copies of `M`.

## The contragredient calculation

On `M^*`, use column coordinates and `rho(g)=g^(-T)`.  With `E_ij` the
matrix units, `(MMP1)` gives

```text
rho(q)=1+(1/2)E_12,              rho(s)=1+(1/2)E_23,
rho(A)=1-2E_21,
rho(B)=diag(1/2,2,1)-2E_32.                           (MMP5)
```

Consequently

```text
rho(X)=-E_11-(1/2)E_12-E_23.                           (MMP6)
```

Indeed the two summands before subtracting the identity are

```text
rho(A)(1-rho(q))=-(1/2)E_12+E_22,
rho(B)(1-rho(s))=-E_23+E_33.                           (MMP7)
```

It follows that

```text
ker rho(X)=K(-1/2,1,0)^T.                              (MMP8)
```

Next

```text
u=1+E_13-(1/2)E_23,
rho(u)=1-E_31+(1/2)E_32,
rho(r)=1+E_32,
rho(h^(-1))=h.                                         (MMP9)
```

Substitution in the second row of `(MMP3)` gives

```text
rho(Y)
 =(E_31-(1/2)E_32)(-(1/2)E_12)-hE_32
 =-E_32.                                               (MMP10)
```

The operator in `(MMP10)` is nonzero on the spanning vector in `(MMP8)`.
Hence the common kernel is zero on `M^*`.

All entries used above lie in the prime subfield.  Frobenius therefore
fixes every displayed coefficient, so the same two calculations apply
verbatim to every `M^(j)` and `(M^*)^(j)`.  On the trivial module,
`rho(X)=-1`, so the common kernel is again zero.

## Extension closure

Suppose

```text
0 -> V_0 -> V -> V_1 -> 0.                              (MMP11)
```

is an exact sequence of `KF`-modules and `(MMP4)` is zero on `V_0` and
`V_1`.  If `lambda` lies in the common kernel on `V`, its image lies in the
common kernel on `V_1`, hence is zero.  Thus `lambda` belongs to `V_0`; its
common-kernel equations there then imply `lambda=0`.  Induction on a
composition series proves `(MAM4)` for every `V` in `S_min`.

Finally, `(MMP3)--(MMP4)` isolate the unproved universal step without any
representation-theoretic ambiguity: arbitrary-module vanishing is exactly
the statement that the two Fox rows have no common kernel on any finite
`KF`-module, equivalently the corresponding one-sided ideal is the whole
finite group algebra.  The calculation above proves that only on the stated
Serre sector.

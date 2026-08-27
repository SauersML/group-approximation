---
rg: 2
id: positive-fixed-corner-three-cycle-diagonalization-proof
kind: route
title: Diagonalize QXQ and orthogonalize the deleted three-cycle spans
target: positive-fixed-corner-cubic-energy-charges-deleted-rank
requires:
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
---

Choose an orthonormal eigenbasis `q_i` of `C=QXQ`, with eigenvalues
`c_i in (0,a_0]`, and put

```text
v_i=P X q_i/sqrt(1-c_i^2).                            (PFD1)
```

The `v_i` are orthonormal and `A v_i=-c_i v_i`.  On the orthogonal
complement of their span inside `PH`, `A` is already an involution and agrees
with `X`.  Thus `X_0=sgn(A)` replaces the eigenvalue `-c_i` by `-1` on each
`v_i` and changes nothing elsewhere.

Write `Y=XU`.  Since `U` fixes `QH` pointwise,

```text
Yq_i=Xq_i.
```

For `r,s in {0,1,2}`, unitarity and `Y^3=1` give

```text
<Y^r q_i,Y^s q_j>
 = delta_(ij)                         if r=s,
 = c_i delta_(ij)                    if r!=s.          (PFD2)
```

Hence the cyclic spaces

```text
K_i=span(q_i,Yq_i,Y^2q_i)
```

are mutually orthogonal.  Extend `X_0` by the identity on `QH`.  On each
`K_i`, the calculation in
`deleted-fixed-line-first-cubic-has-explicit-positive-spectrum` applies with
`a=c_i`; off their sum, the extended polar involution agrees with `X`, so
the cubic stays exact.  Frobenius squares add across the orthogonal `K_i`,
giving

```text
||(X_0U_0)^3-1||_F^2=sum_i f(c_i)=Tr_Q f(C).           (PFD3)
```

Each summand has residual rank at most two.  Finally,

```text
d/dt log(f(t)/4)
 =-2/(1-t)+2/(1+2t)-3/(1+t)
 =-3(1+3t)/((1-t)(1+2t)(1+t))<0,                     (PFD4)
```

which proves `(PFC3)`.


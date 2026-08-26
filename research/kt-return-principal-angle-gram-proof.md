---
rg: 2
id: kt-return-principal-angle-gram-proof
kind: route
title: Compare the two off-diagonal edge blocks and orthonormalize a word basis
target: kt-return-expectation-pays-one-full-edge-principal-angle
requires: []
---

Work on the finite-dimensional Hilbert space

```text
K=L2(M_d,tr_d).
```

Let `W=Ad(T)` and retain `P=E_B`.  The two off-diagonal blocks

```text
A=(1-P)WP,             R=(1-P)W^*P                     (KPP1)
```

have the same singular values.  Indeed, on `PK`, if `C=PWP`, then

```text
A^*A=1-C^*C,             R^*R=1-CC^*.                 (KPP2)
```

The square matrices `C^*C` and `CC^*` have the same spectrum.  Hence

```text
||R||_op=||A||_op<=||A||_HS.                            (KPP3)
```

The unit vector `b=phi(gamma)` belongs to `B`.  Therefore

```text
||(1-P)T^*bT||_2<=||R||_op.                             (KPP4)
```

On the other hand, `(KPA3)` gives

```text
||P(T^*bT)||_2<=q+eta_h.
```

Since `T^*bT` is a unitary of normalized `L2` norm one,

```text
||(1-P)T^*bT||_2^2>=1-(q+eta_h)^2.                     (KPP5)
```

Combining `(KPP3)--(KPP5)` proves `(KPA4)`.

For the Gram formula, regard the column `b=(b_1,...,b_m)` as a linear map
from `C^m` onto `B`.  Its Gram matrix is `G=b^*b`.  Since the list is a
basis, `G` is positive definite, and `bG^(-1/2)` is an orthonormal basis of
`B`.  Applying `A` and summing the squared norms gives

```text
||A||_HS^2
 =Tr(G^(-1/2) H G^(-1/2))
 =Tr(G^(-1)H),                                          (KPP6)
```

which is `(KPA7)`.  Positivity of `H` and
`Tr(H)=sum_i||y_i||_2^2` give

```text
Tr(G^(-1)H)
 <=||G^(-1)|| Tr(H)
 <=lambda^(-1) sum_i epsilon_i^2.                       (KPP7)
```

Finally, if

```text
b_i=a_(i,1)...a_(i,ell_i),
```

where each `a_(i,j)` is `phi(delta)` or its adjoint, conjugate the product
by `T` and replace the factors one at a time by
`phi(t delta t^(-1))` or its adjoint.  All intermediate factors are
unitaries, so telescoping gives `(KPA9)` and

```text
epsilon_i<=ell_i epsilon.                               (KPP8)
```

For completeness, with

```text
d_phi(a,b)=||phi(ab)-phi(a)phi(b)||_2,
```

the two fixed covariance errors obey

```text
||T phi(delta)T^*-phi(t delta t^(-1))||_2
 <=d_phi(t,delta)+d_phi(t^(-1),t)+d_phi(t delta,t^(-1)),

eta_h
 <=d_phi(t^(-1),gamma t)+d_phi(gamma,t)+d_phi(t^(-1),t). (KPP9)
```

This proves the ordinary-defect assertion and completes the derivation.

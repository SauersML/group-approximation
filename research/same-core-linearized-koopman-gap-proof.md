---
rg: 2
id: same-core-linearized-koopman-gap-proof
kind: route
title: Differentiate the same-core cubic identity and apply the exact Koopman gauge-distance formula
target: same-core-gauge-rows-control-linearized-koopman-inverse-energy
requires:
  - koopman-weighted-energy-is-linearized-gauge-distance
---

Put `B=XT` and `alpha=Ad(B)`.  Because `A` commutes with `T`,

```text
alpha(A)=Ad(X)(A).
```

The two left-trivialized row differentials in `(SCK2)` are therefore

```text
L_2 A=A+alpha(A),
L_3 A=A+alpha(A)+alpha^2(A).
```

Consequently there is the exact linear identity

```text
A=L_3 A-alpha(L_2 A).                                  (1)
```

Since `alpha` is an `L^2` isometry, `(1)` gives

```text
||A||_2<=||L_2 A||_2+||L_3 A||_2,
||A||_2^2<=2(||L_2 A||_2^2+||L_3 A||_2^2).            (2)
```

Let `A_0=A-E_(ker D)(A)`.  The minimum-norm inverse of `D A` is `A_0`,
while `||A_0||_2<=||A||_2`.  By the exact spectral identity in
`koopman-weighted-energy-is-linearized-gauge-distance`,

```text
sum_t t^(-2)||P_t D A||_2^2
 <=||D^dagger D A||_2^2
 =||A_0||_2^2.
```

Combining this with `(2)` proves `(SCK3)`.  The argument takes place in the
whole finite tracial matrix algebra.  Direct sums, multiplicity blocks, and
off-diagonal elements of `{T}'` therefore require no separate tensorization
argument.  Notice that neither `X^2=1` nor `(XT)^3=1` was used; the identity
is a global Fox-row identity at every base point, although its conclusion is
only differential.

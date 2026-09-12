---
rg: 2
id: compact-semialgebraic-lojasiewicz-head-collapse-proof
kind: route
title: Compact semialgebraic separation gives the bounded-dimension head modulus
target: bounded-dimension-jacobson-head-has-algebraic-collapse
requires:
  - binary-jacobson-core-is-weakly-sofic-with-fd-head-radical
  - binary-jacobson-steinberg-cover-is-elementary
  - qutrit-complementary-jacobson-signs-minimal-router-finite
---

## The finite presentation really exists

The binary Jacobson ring has the finite unital ring presentation

```text
J=F_2<S,T | TS=1>.
```

Krstic--McCool, Theorem 3, says that `St_r(R)` is finitely presented
for every finitely presented ring `R` and every `r>=4`. Thus
`St_28(J)` is finitely presented. The established calculation
`bsr(J)=2`, `K_2(J)=0`, together with unstable K-two stability,
gives

```text
ker(St_28(J)->E_28(J))=0.
```

Hence `G=E_28(J)` itself is finitely presented. The use of a finite
presentation below is therefore unconditional.

## A fixed matrix size

Write the finite presentation as

```text
G=<Sigma | R>
```

and fix `n>=1`. On the compact real algebraic set

```text
X_n=U(n)^Sigma
```

define the nonnegative functions

```text
F_n(U)=sum_(r in R) ||r(U)-I||_(2,n)^2,
G_n(U)=||w(U)-I||_(2,n)^2.                              (BLP1)
```

Both functions are continuous and semialgebraic. Indeed a group word is
a polynomial in the real and imaginary matrix entries after every inverse
is replaced by the adjoint, and normalized Hilbert--Schmidt norm squared
is a real polynomial on `X_n`.

If `F_n(U)=0`, then every presentation relator is exact, so `U`
defines a homomorphism `G->U(n)`. Every finite-dimensional unitary
representation of `G` kills the finitary kernel and hence kills the
head word `w). Therefore

```text
{F_n=0} subset {G_n=0}.                                  (BLP2)
```

The compact semialgebraic Lojasiewicz inequality applied to `(F_n,G_n)`
now gives constants `A_n<infinity` and `theta_n>0` such that

```text
G_n(U) <= A_n F_n(U)^theta_n       for every U in X_n.   (BLP3)
```

No limiting representation or choice of a nearby exact tuple is needed
for this step. The zero-set inclusion `(BLP2)` is exactly the hypothesis
of the semialgebraic inequality.

Put

```text
delta(U)=max_(r in R)||r(U)-I||_(2,n).
```

Then `F_n(U)<=|R| delta(U)^2`. Taking square roots in `(BLP3)`
gives

```text
||w(U)-I||_(2,n)
 <= sqrt(A_n) |R|^(theta_n/2) delta(U)^theta_n.          (BLP4)
```

For a fixed `D`, take

```text
alpha_D=min_(1<=n<=D) theta_n,
C_D=max_(1<=n<=D) sqrt(A_n)|R|^(theta_n/2).
```

When `delta<=1`, `delta^theta_n<=delta^alpha_D`, so `(BLP4)`
proves `(BDJ2)` simultaneously for every `n<=D`.

If an approximate representation sequence has head defect at least
`epsilon>0` and presentation defect tending to zero, `(BDJ2)`
excludes every bounded subsequence of dimensions. Its dimensions must
therefore tend to infinity.

## Why the four mixed quarters do not make the constants uniform

Let

```text
F=<C,g_1,H,U,V>.
```

The complementary-sign calculation proves that `F` is finite and
contains the nonidentity head involution `H`. In the left regular
representation of `F), every relation internal to this packet is exact,
whereas

```text
||lambda(H)-I||_2^2
 =2-2 Re tau(lambda(H))
 =2.                                                     (BLP5)
```

Thus the packet has zero internal defect and head defect `sqrt(2)`.
This exact model contains all four sign projections and every
`g_1`-routed cross term at once. Consequently neither complementary
sign recombination nor finite-dimensional compactness for that
subpresentation can force the head to collapse.

The global estimate works because the full relator zero set consists of
representations of `G`, where the head is erased. A dimension-free
estimate would require uniform control of `A_n` and `theta_n` as
`n->infinity`. Compact semialgebraic separation supplies no such
control. That missing uniformity is precisely the normalized-HS
ultraproduct gate, so this proof does not decide whether head-retaining
microstates exist.

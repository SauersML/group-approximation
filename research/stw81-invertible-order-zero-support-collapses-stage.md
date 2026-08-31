---
rg: 2
id: stw81-invertible-order-zero-support-collapses-stage
kind: route
title: Use the invertible order-zero support to expose a finite-dimensional character
target: stw81-positive-scalar-order-zero-approximation-is-scalar
requires: []
---

Fix `a in D` with `norm(a)<=1`, apply (PSO2) to `{1_D,a}`, and assume
`epsilon<c`.  Put

```text
q=phi(1_F),                     x=phi psi(1_D).
```

Because `psi(1_D)<=1_F` and `phi` is positive,

```text
0<=x<=q<=1_D.                                           (ISC1)
```

The unit estimate gives `x>=(c-epsilon)1_D`, so `q` is invertible.  The
supporting-homomorphism description of order-zero maps therefore occurs
inside `D` itself:

```text
phi(z)=q pi(z)=pi(z)q,             z in F,             (ISC2)
```

for a unital star homomorphism `pi:F->D`.  Concretely, invertibility lets
one write `pi(z)=q^(-1)phi(z)`; the order-zero relations make this a star
homomorphism and `pi(1_F)=1_D`.

Every projection in `pi(F)` is a projection in `D`, hence is zero or one.
A finite-dimensional C-star algebra whose unital image has no nontrivial
projections can only have scalar image.  Thus `pi` factors through a
character

```text
chi:F->C,                     pi(z)=chi(z)1_D.          (ISC3)
```

Consequently

```text
phi psi(b)=omega(b)q,
omega=chi o psi:D->C,                                  (ISC4)
```

where `omega` is positive.  Let `lambda=omega(1_D)`.  From (ISC1) and the
unit estimate, `lambda>=c-epsilon>0`.  Positivity gives

```text
abs(omega(a))<=lambda.
```

Set `mu=omega(a)/lambda`, so `abs(mu)<=1`.  Using (PSO2) at `a` and at the
unit,

```text
norm(ca-mu c1_D)
 <=norm(ca-omega(a)q)
   +abs(mu)norm(lambda q-c1_D)
 <2epsilon.                                            (ISC5)
```

Hence `dist(a,C1_D)<2epsilon/c`.  Since `epsilon` is arbitrary, `a` is
scalar.  This holds for every contraction in `D`, proving (PSO3).

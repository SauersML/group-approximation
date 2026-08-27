---
rg: 2
id: profinite-free-compressors-retain-coefficient-residual
kind: claim
title: Profinite automorphic models of free compressors retain every base coefficient exactly
distinct_from:
  kt-two-compressor-irrep-flow-has-profinite-stationary-points: That keeps only the scalar Plancherel distribution stationary under the two Kun--Thom compressor flows; this retains the norm of a named algebraic base coefficient and implements both covariance rows exactly.
  opposite-transvections-are-free-but-finite-lamp-windows-close: That builds finite Bernoulli models for each bounded positive-cone lamp window and fails the stabilizer-moved lamp row; this gives exact coefficient-bearing representations of the free multiple-HNN covariance presentation on the whole finite quotient of the base.
  rf-amenable-two-cell-retains-coefficient: That uses Folner sets and has small boundary error for amenable joint holonomy; this has no Folner set and no covariance error, because finite quotient blindness turns every proper compressor into an automorphism.
---

**ESTABLISHED FREE-HOLONOMY FENCE.**  Let `Lambda` be a group with injective
endomorphisms `alpha_1,...,alpha_r`.  Assume the following simultaneous
profinite automorphic approximation property: for every finite set
`T subset Lambda` there are a finite quotient

```text
q_T:Lambda->Q_T
```

which is injective on `T`, and automorphisms `bar(alpha_i)` of `Q_T` such
that

```text
q_T alpha_i=bar(alpha_i) q_T.                            (PFC1)
```

Form the free multiple ascending-HNN covariance presentation

```text
H=<Lambda,t_1,...,t_r |
    t_i g t_i^(-1)=alpha_i(g), g in Lambda>.             (PFC2)
```

There are no relations among the stable letters beyond covariance.  Then
for every algebraic coefficient `b in C[Lambda]` there is an exact
finite-dimensional representation `rho_b` of `(PFC2)` satisfying

```text
||rho_b(b)||_2=||lambda_Lambda(b)||_2.                   (PFC3)
```

Moreover, the stable letters may be tensored with an arbitrary
finite-dimensional representation of the free group `F_r` without changing
`(PFC3)` or any covariance row.  Thus they may simultaneously be made
canonical on any prescribed finite window of **pure stable-letter words**.

## Application to the free Kun--Thom compressor pair

Let `Gamma<G` be the residually finite Kun--Thom actor pair and let

```text
A=I+E_12,                    B=I+E_21.                   (PFC4)
```

Put `alpha_A=Ad(A)|_Gamma` and `alpha_B=Ad(B)|_Gamma`.  For any finite
`T subset Gamma`, choose a finite quotient `q:G->K` separating all pair
differences from `T`, and put `Q=q(Gamma)`.  Since

```text
A Gamma A^(-1)<=Gamma,       B Gamma B^(-1)<=Gamma,
```

conjugation by `q(A)` and by `q(B)` injects the finite group `Q` into
itself, hence is onto.  These two conjugations give `(PFC1)` simultaneously.
Consequently `(PFC3)` applies even though `A,B` generate a free positive
compression monoid and its right boundary has uniform expansion.

For the bounded-type coefficient of
`one-bounded-type-coefficient-separates-unbounded-exits`, namely

```text
b=z(1-a),
```

the same exact representations satisfy

```text
||rho_b(z(1-a))||_2
 >=(1-epsilon)sqrt(tau_B(z)),                            (PFC5)
```

while every defining covariance relator in `(PFC2)` has zero defect.

Thus nonamenable free-semigroup expansion does **not** compile a shared
bounded-type coefficient into normalized-HS word energy.  The abstract
free branching is invisible because a finite-dimensional representation is
allowed to fold all sufficiently deep stable-letter words through a finite
automorphism group.  Tensoring by finite quotients of `F_r` shows that this
is not caused by collapsing any preassigned bounded free-word window.

The conclusion is deliberately limited to the covariance presentation.
The finite quotient models still collapse the Kun--Thom
`Gamma`-moved-site lamp correlation, exactly as in
`free-compressor-tree-has-constant-first-hit-mover-mass`.  Therefore a live
nonamenable two-compressor cell must couple the named coefficient to that
stabilizer-sensitive mixed return, or impose another relation which cannot
survive the simultaneous profinite automorphic folding.  Free holonomy plus
a shared coefficient occurrence is not enough.

The first literal coupling to that return is fenced too.
`kt-payload-annihilator-mixed-return-has-profinite-countermodels` imposes the
full finite Kazhdan stabilizer packet and multiplies the arithmetic moved-site
difference by `z(1-a)`.  In common finite quotients the return word falls
back into the finite image of `Gamma`, so the moved-site difference is zero
while the coefficient retains its full regular norm.  Thus the surviving
relation must prevent that collapse by reflecting the payload into the
moved-site carrier; an annihilator product is insufficient.

DERIVATION
profinite-free-compressor-coefficient-proof

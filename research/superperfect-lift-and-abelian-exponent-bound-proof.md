---
rg: 2
id: superperfect-lift-and-abelian-exponent-bound-proof
kind: route
title: Lift every projective sector and bound its residual scalar by relator exponents
target: projective-jacobson-multipliers-have-a-linear-head-bound
requires:
  - binary-jacobson-steinberg-cover-is-elementary
  - binary-jacobson-core-is-weakly-sofic-with-fd-head-radical
  - bounded-dimension-jacobson-head-has-algebraic-collapse
---

## Superperfectness

For matrix rank at least five, the Steinberg group over a unital ring
is the universal central extension of the elementary group. Over

```text
J=F_2<S,T | TS=1>,
```

the established stable-rank calculation gives `K_2(J)=0` and
identifies `St_28(J)->E_28(J)` with an isomorphism. Therefore

```text
H_1(G,Z)=0,                  H_2(G,Z)=0.                 (PJB3)
```

The first equality also follows directly from the elementary
commutator relations.

Let `bar rho:G->PU(d)` be any projective unitary representation.
Pulling back `U(d)->PU(d)` gives a central extension of `G) by a
subgroup of the circle. Equation `(PJB3)`, or equivalently the
universal property of the now trivial Steinberg cover, splits this
extension. Thus `bar rho` has a genuine unitary lift

```text
rho:G->U(d).                                             (PJB4)
```

## One projective sector

First suppose every relator value `r(U)` is a scalar. The projective
classes of the generator matrices define a homomorphism

```text
bar rho:G->PU(d).
```

Choose the lift in `(PJB4)`. For each generator there is a scalar
`alpha_x` such that

```text
U_x=alpha_x rho(x).                                     (PJB5)
```

For a free word `v`, let `e(v) in Z^X` be its generator exponent
vector and use the abbreviation

```text
alpha(e(v))=product_(x in X) alpha_x^(e_x(v)).
```

Then

```text
v(U)=alpha(e(v)) rho(v).                                (PJB6)
```

Every exact finite-dimensional representation of `G` kills the
finitary kernel, so `rho(w)=I`. Therefore `w(U)` is the scalar
`alpha(e(w))).

Since `G` is perfect, the exponent vectors of the finite relator set
generate all of `Z^X`. Fix integers `n_r`, once and for all, such
that

```text
e(w)=sum_(r in R) n_r e(r),             and put
C_w=sum_(r in R)|n_r|.                                  (PJB7)
```

Equations `(PJB6)--(PJB7)` give

```text
w(U)=product_(r in R) zeta_r^(n_r) I.                   (PJB8)
```

For unit-circle scalars,

```text
|product_r zeta_r^(n_r)-1|
 <=sum_r |n_r| |zeta_r-1|.                              (PJB9)
```

This proves the desired estimate on one block.

## Arbitrarily many sectors

Return to the reducing decomposition in `(PJB1)`. Apply the one-block
argument on each `H_j`; the same integers `n_r` work in every
dimension. Put `p_j=dim(H_j)/dim(H)`. Multiplying `(PJB9)` by
`sqrt(p_j)`, taking the `l^2)-norm over `j), and using Minkowski
gives

```text
||w(U)-I||_2
 <=sum_(r in R)|n_r| ||r(U)-I||_2
 <=C_w max_(r in R)||r(U)-I||_2.                        (PJB10)
```

This is `(PJB2)`.

The argument permits arbitrary sector-dependent central characters and
arbitrary dimensions. It fails only when at least one relator error is
genuinely noncentral on every common reducing decomposition, exactly
as asserted in the claim.

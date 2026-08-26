---
rg: 2
id: complementary-private-a3-cross-commutation-proof
kind: route
title: Use top-prefix orthogonality to eliminate every direct complementary private-arm interaction
target: complementary-private-a3-root-packets-cross-commute
requires:
  - complementary-depth-two-a3-whiteheads-have-a6-gauge-model
  - complementary-private-weyl-loops-have-s3-square-gauge-model
---

For binary words `mu,nu,rho,sigma`, Leavitt prefix cancellation gives

```text
(s_(0 mu)t_(0 nu))(s_(1 rho)t_(1 sigma))
 =s_(0 mu)(t_(0 nu)s_(1 rho))t_(1 sigma)=0,           (CACP1)
```

because the middle prefixes begin in different letters.  Interchanging
zero and one proves the other product is zero.  Substitution of the six
coefficients in `(CAC2)` and of `q_i` proves `(CAC3)`.

Write `x_uv(r)=I+e_uv r`.  For any two roots and `r_0r_1=r_1r_0=0`,

```text
(e_uv r_0)(e_kl r_1)=delta_(v,k)e_ul(r_0r_1)=0,
(e_kl r_1)(e_uv r_0)=delta_(l,u)e_kv(r_1r_0)=0.       (CACP2)
```

Thus the two elementary matrices commute regardless of their incidence.
This includes an opposite-root pair: both possible diagonal cross terms in
the corresponding two-by-two block vanish.  Applying `(CACP2)` to
`a_0^-a_1=0` and `q_1c_0^-=0` proves `(CAC4)--(CAC5)` at the displayed
EL20 coordinates.  Factorwise application proves the word-level statement.

Finally the two direct factors in the finite model `(CPW5)--(CPW6)` commute,
so it realizes every new cross-commutation.  Its already-computed diagonal
product `DE` has order three.  Hence none of these relations can imply a
native ungauged bridge or `DE=1`.

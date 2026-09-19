---
rg: 2
id: stw87-invariant-mean-retraction-coset-gap-proof
kind: route
title: Compress a regular covariant representation and test invertibility on cosets
target: stw87-invariant-mean-retraction-has-coset-order-zero-gap
requires: []
---

Let `(pi_m,H_m,xi_m)` be the GNS representation of the invariant mean.
Invariance gives a unitary representation implementing the translation
action and fixing `xi_m`.  Form the regular covariant representation on
`ell^2(G) tensor H_m`.  With the convention

```text
pi_tilde(f)(delta_h tensor eta)
  = delta_h tensor pi_m(alpha_(h^-1)(f))eta,
```

the group unitaries act by left translation on the first tensor factor.
The isometry

```text
V:ell^2(G)->ell^2(G) tensor H_m,
V delta_h=delta_h tensor xi_m
```

therefore satisfies

```text
V* pi_tilde(f) lambda_t V = m(f) lambda_t.             (3)
```

Indeed, the only nonzero matrix coefficient has row `th` and column `h`,
and its scalar value is
`m(alpha_((th)^-1)(f))=m(f)`.  Compression by `V` is u.c.p., so (3) extends
to a u.c.p. map `P_m` on the reduced crossed product.  It fixes each
`lambda_t`; hence its range is `C*_r(G)` and its restriction to that range
is the identity.  It is therefore a conditional expectation, and (3)
proves formula (1).

Write the left cosets as `C_1,...,C_k` and put `p_i=1_(C_i)`.  Translation
invariance and `sum_i p_i=1` give

```text
m(p_i)=1/k,
(P_m phi)(e_i)=(1/k)1.                                (4)
```

Let `theta:C^k->C*_r(G)` be c.p.c. and order zero, and write
`a_i=theta(e_i)`.  The `a_i` are positive and pairwise orthogonal.  If all
of them had distance strictly less than `1/k` from `(1/k)1`, then each
`a_i` would be invertible: its spectrum would lie in `(0,2/k)`.  Two
invertible elements cannot have zero product, contradicting
`a_i a_j=0` for `i!=j`.  Consequently

```text
max_i norm(a_i-(1/k)1) >= 1/k.                         (5)
```

The zero map is c.p.c. and order zero and attains equality in (5).  This
proves the exact formula (2).

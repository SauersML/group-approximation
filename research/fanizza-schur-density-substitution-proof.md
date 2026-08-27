---
rg: 2
id: fanizza-schur-density-substitution-proof
kind: route
title: Replace every forbidden projection in the sparse certificate and apply Cauchy--Schwarz
target: fanizza-schur-density-substitution
requires:
  - fanizza-bcs-polynomial-doubling-tape
  - fanizza-final-bcs-has-fixed-nonlinear-menu
  - schur-predicate-is-character-density-difference
---

The Fanizza decomposition expresses `R_n` as a sum of left/right polynomial
multiples of defining BCS relators, with certificate size bounded by
`C((n+1)m)^k`. Separate the finitely many nonlinear relator occurrences from
the linear and commutation occurrences. For every nonlinear occurrence,
`(CDF2)` gives the exact replacement

```text
P_(f_c)=2D_c G_c.
```

This proves `(FDS2)` without changing the number of certificate terms. The
Fanizza menu is fixed and its Schur packets have uniformly bounded size, so
the factors `2D_c`, character-table coefficient norms, and fixed
exactification moduli are absorbed into constants independent of `n,m`, and
matrix dimension. This proves `(FDS3)`.

Evaluate the decomposition on a unitary tuple. By the definition of
certificate size, every left/right coefficient has the stated uniform norm
bound. Triangle inequality bounds the background terms by the first term of
`(FDS4)`. For the density terms, Cauchy--Schwarz gives

```text
sum_(ell in L_n)||A_ell(2D_cG_c)B_ell||_2
 <= C sqrt(|L_n|) (sum_(ell in L_n)||G_c||_2^2)^(1/2).
```

Use `|L_n|<=C((n+1)m)^k` to obtain the second term of `(FDS4)`. Fixed packet
exactification changes each finite word average by its dimension-independent
Lipschitz constant and is included in `E_pkt`.

Finally `(FDS5)` and bounded occurrence overlap replace `E_G(n)` by a fixed
multiple of ordinary group-relator energy. Substitution in `(FDS4)` leaves a
polynomial level cost, which is summable against Fanizza's exponential
weights. This proves the claimed reduction of the remaining groupification
obligation.

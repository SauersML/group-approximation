---
rg: 2
id: dephasing-inverse-forces-monomial-proof
kind: route
title: Fourth-moment concentration plus Birkhoff selects a monomial support
target: dephasing-inverse-forces-monomial
requires: []
---

Set

```text
kappa(U) = 1 - d^{-1} sum_{i,j} |u_ij|^4
         = 1 - tau_d(P_U P_U^T).
```

Since `|tau(A)| <= ||A||_2`, the hypothesis gives `kappa(U) <= eps`.
Write `P_U` as a convex combination of permutation matrices. Averaging the
normalized inner products with those permutations shows that some permutation
`sigma` satisfies

```text
d^{-1} sum_i |u_{i,sigma(i)}|^2
  >= d^{-1} sum_{i,j}|u_ij|^4
  = 1-kappa(U).
```

Let `M` be the monomial matrix supported on `sigma`, with the phase of its
`i,sigma(i)` entry chosen to match `u_{i,sigma(i)}`. Then

```text
d_2(U,M)^2
 = 2 - (2/d) sum_i |u_{i,sigma(i)}|
 <= 2 - (2/d) sum_i |u_{i,sigma(i)}|^2
 <= 2 kappa(U)
 <= 2 eps.
```

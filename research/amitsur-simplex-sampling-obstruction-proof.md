---
rg: 2
id: amitsur-simplex-sampling-obstruction-proof
kind: route
title: Replace the signed permutation monomials by a regular simplex Gram table
target: raw-amitsur-permutation-sampling-has-factorial-gap-loss
requires:
  - raw-gram-rank-overflow-has-no-constant-local-gap
  - one-sided-amitsur-oracle-has-bounded-fock-model
---

Absorb the alternating signs into the permutation monomials.  The prefix-code
calculation makes their Fock Gram matrix `I_N`, proving `(RAP2)--(RAP3)`.

Apply `raw-gram-rank-overflow-has-no-constant-local-gap` with `r=N-1`.  Its
regular simplex has Gram matrix

```text
G_S=(N/(N-1)) I_N-(1/(N-1)) J_N,                         (RAP7)
```

so `G_S 1=0`, its diagonal is one, and all off-diagonal entries are
`-1/(N-1)`.  Restriction to `q` labels differs from the identity by a matrix
with zero diagonal and constant off-diagonal magnitude `1/(N-1)`, whose
operator norm is `(q-1)/(N-1)`.  Lipschitz continuity gives `(RAP6)`.

---
rg: 2
id: finite-edge-character-overlap-proof
kind: route
title: Conjugate the central Fourier idempotents and their commutant averages
target: finite-edge-reynolds-overlap-follows-character-transport
requires:
  - finite-character-idempotents-have-exact-hnn-transport
---

Fourier inversion gives

```text
e_(+,chi)=|Z_+|^-1 sum_z conjugate(chi(z))rho(z).
```

Conjugate term by term using `(FEO1)` and change variables through `phi` to
obtain `(FEO3)`.  The Reynolds projection is the composition of compression
to the character corner with the average of `Ad_(rho(h))` over the finite
group.  Conjugating both operations by `Ad_(rho(t))` changes the corner by
`(FEO3)` and the average by the bijection `h |-> phi(h)`, proving `(FEO4)`.

Distinct central-character corners are orthogonal.  Therefore the ranges of
`T R_(+,chi)T^*` and `R_(-,psi)` are orthogonal when
`psi!=sigma(chi)`, and `(FEO5)` is zero.  Equation `(FEO6)` is the already
established exhaustive paired-frame character calculation.

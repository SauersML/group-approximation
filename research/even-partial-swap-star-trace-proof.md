---
rg: 2
id: even-partial-swap-star-trace-proof
kind: route
title: Decompose the common-source star into one cycle and two fixed complements
target: even-partial-swap-star-has-canonical-trace-floor
requires: []
---

Identify every range `P_iH` with the common source `QH` using `S_i`.  On the
orthogonal sum of the source and the `k` ranges, the swaps `J_i` are the star
transpositions, so their product is a `(k+1)`-cycle and has trace zero.  On
the top complement every factor is `+1`; on the bottom complement every
factor is `-1`, whose even product is `+1`.  Normalizing in the two-copy
space gives

```text
tau_2(J_1...J_k)=1-(k+1)/2 tau(Q).
```

Orthogonality implies `k tau(Q)<=1`, hence the right side is at least
`(k-1)/(2k)`.  Replacing each swap by an `epsilon`-close decoded word changes
the product trace by at most `k epsilon`, proving the robust statement.

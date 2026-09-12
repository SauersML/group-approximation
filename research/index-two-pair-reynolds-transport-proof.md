---
rg: 2
id: index-two-pair-reynolds-transport-proof
kind: route
title: Conjugate both subgroup averages and Fourier-decompose the elementary-abelian target
target: index-two-reynolds-atoms-have-orthogonal-hnn-transports
requires:
  - central-sign-assignment-atom-is-index-two-reynolds-surplus
  - canonical-types-extend-every-finite-bass-serre-actor
---

Since `H` has index two in `C`, `e_C<=e_H`; hence `e_H-e_C` is a projection,
and similarly on the target.  Averaging `(ITH2)` over `H` and over `C` gives

```text
u e_H u^(-1)=e_(H'),          u e_C u^(-1)=e_(C'),
```

so subtraction proves `(ITH4)`.  Averaging the approximate covariance rows
and applying the triangle inequality proves `(ITH5)`.

For elementary abelian `T`, the trivial-character projection is `e_T`, while
`e_(ker chi)` is the sum of the trivial and `chi` character projections.
Their difference is therefore `D_chi`; character orthogonality gives
`(ITH7)`.  The final warning follows from the canonical trace calculation
and `canonical-types-extend-every-finite-bass-serre-actor`.

---
rg: 2
id: exact-projective-arithmetic-transfer-proof
kind: route
title: Kill scalar relators in the adjoint representation and apply exact arithmetic transfer
target: exact-projective-arithmetic-tuples-obey-transfer
requires:
  - codense-gap-controls-exact-projective-tuples
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Scalar relators vanish under `Ad`, so an exact projective tuple on `C^d`
gives an honest `d^2`-dimensional representation `beta` on `M_d`.  The
rank-one co-dense `tau` theorem and the higher-rank property-(T) co-density
theorem supply `(CDG1)--(CDG2)`.  Apply
`codense-gap-controls-exact-projective-tuples`; its key identity is

```text
||[Ad(U),Ad(rho(g))]_add||_2^2=2e(U,rho(g)).
```

This gives `(EPA3)` uniformly in `d` and in the scalar multiplier class.

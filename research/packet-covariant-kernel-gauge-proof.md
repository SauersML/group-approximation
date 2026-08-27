---
rg: 2
id: packet-covariant-kernel-gauge-proof
kind: route
title: Put the free kernel in growing finite regular gauges behind the named packet action
target: packet-covariant-kernel-gauge
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - fixed-packet-correction-retains-multiplicity-gauge
---

Equation `(PCG1)` says that `pi(b_i)^*X_i` commutes with the irreducible
packet algebra, proving `(PCG2)`; finite-group averaging and polar correction
give the `3epsilon` robust form exactly as for any fixed packet normalizer.
Multiplying the tensor factors proves `(PCG3)--(PCG4)`.

Choose a descending residual chain in the free group whose intersection is
trivial.  Its intersections with the infinite finite-index subgroup `N`
also descend trivially, so the finite images `H_k=q_k(N)` have unbounded
order.  As an `H_k`-module, `ell^2(Q_k)` is
`[Q_k:H_k] lambda_(H_k)`.  The commutant dimension is therefore

```text
[Q_k:H_k]^2 |H_k|=|Q_k|^2/|H_k|,
```

which proves `(PCG6)`.  Tensoring with the fixed outer BCS/Schur packet
preserves all outer ranks and covariance, while every kernel-fixed adjoint
subspace is contained in `(PCG7)`.

After arbitrary additional relators are specialized on the outer type, the
same proof works for any canonical active models with vanishing `N`-commutant
density.  Residual finiteness plus infinite image of `N` supplies such models
by the identical regular-quotient calculation.  This proves the stated
criterion `(PCG8)` and the tensor-gauge boundary.

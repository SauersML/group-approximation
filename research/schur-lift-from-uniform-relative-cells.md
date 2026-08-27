---
rg: 2
id: schur-lift-from-uniform-relative-cells
kind: route
title: Uniform relative cells plus coherent type accounting give the doubling-tape compiler
target: finite-dimensional-schur-lift-of-doubling-tape
requires:
  - uniform-relative-clifford-tape-cell
  - coherent-sequential-schur-tape-payment
  - shared-overlap-controls-packet-multiplicity-vector
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Use the uniform relative-cell theorem inductively along the nested tower.
The coherent-payment theorem chooses or accounts for the resulting overlap
corrections, applies the exact factor-two restriction matrix on active sectors,
and charges inactive sectors and discarded corners by the polynomial Fanizza
certificate budget. Its first clause is `(SDL1)` and its remaining clauses sum
to `(SDL2)`. These are exactly the conclusions of
`finite-dimensional-schur-lift-of-doubling-tape`.

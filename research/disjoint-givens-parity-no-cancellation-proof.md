---
rg: 2
id: disjoint-givens-parity-no-cancellation-proof
kind: route
title: Separate the matrix-unit support of every rotation plane
target: disjoint-givens-planes-cannot-cancel-parity-terms
requires:
  - one-binary-marginal-block-escape
  - rstar-hadamard-escape-violates-term-c4
---

On one real rotation plane, direct multiplication of
`U diag((-1)^(a_y),(-1)^(b_y)) U^*` gives `(DGP1)`.  Constant parity makes
the Hamming distance of two distinct assignments even.  In a block-diagonal
direct sum, no other plane has an `(r,s)` matrix entry.  Conjugation by the
diagonal free-phase wordization attaches the unique word
`h_r h_s^(-1)` without changing that matrix support.  Hence neither matrix
coefficients nor their full phase-labelled terms cancel between planes.

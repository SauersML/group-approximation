---
rg: 2
id: affine-frobenius-local-storage-proof
kind: route
title: Clear rational denominators inside the full matrix Frobenius block
target: affine-frobenius-packets-solve-local-row-mask-storage
requires:
  - affine-frobenius-group-has-almost-full-simple-block
---

Dirichlet supplies primes `p=1 mod D`.  Since `D` divides `p-1`, the ranks in
`(AFP1)` are integers summing to `p-1`; choose orthogonal coordinate
projections of those ranks inside `M_(p-1)(C)`.  The block is the algebraic
corner `q_p C[H_p]q_p`, so every chosen matrix lies in the finite group
algebra.  Add a PVM on the complementary central summand `e_N` to obtain a
unital PVM.  Formula `(AFB2)` gives the exact deficit `1/p`.


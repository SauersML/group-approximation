---
rg: 2
id: support-failure-packet-has-explicit-hs-payment-proof
kind: route
title: Diagonalize the baseline Laplacian in the Pauli-word basis
target: support-failure-packet-has-explicit-hs-payment
requires:
  - support-failure-has-fixed-pivot-rank-one-compiler
  - clifford-commutator-rank-is-packet-dimension
  - finite-group-multiplicity-mismatch-pays-hs-energy
---

The leading one-by-one commutation matrix of `A_sub` is `[1]`, so
`clifford-commutator-rank-is-packet-dimension` gives the full matrix algebra
`M_2(C)` and its unique two-dimensional Pauli simple in every fixed selector
sector.  The full matrix has rank one on the three allowed atoms and rank two
on `(0,1)`, proving `(SHP1)` by dimension.

Represent `p_1,q_1` by Pauli involutions `P,Q`.  On the matrix basis
`I,P,Q,PQ`, the sum of the two commutator quadratic forms has eigenvalues
`0,4,4,8`.  For a pair of selector sectors at Hamming distance `h`, each
differing central selector contributes the scalar form `4||T||_2^2`.  The four
eigenvalues are therefore

```text
4h, 4+4h, 4+4h, 8+4h.                                (1)
```

For equal sectors the kernel is the scalar matrices and the first positive
eigenvalue is four.  For unequal sectors `h>=1`, there is no kernel and the
smallest eigenvalue is at least four.  This proves `(SHP2)`.  Apply
`finite-group-multiplicity-mismatch-pays-hs-energy` with `kappa=4` to obtain
`(SHP3)`.

---
rg: 2
id: fano-point-line-permutation-character-proof
kind: route
title: Compare fixed vectors of a matrix and its contragredient
target: fano-points-and-lines-have-the-same-complex-permutation-type
requires:
  - rstar-odd-character-ghost-fiber-is-eight-sectors
---

For `A in GL(3,2)`, its fixed nonzero vectors number
`2^(dim ker(A-I))-1`.  A Fano line is the kernel of a unique nonzero
covector, and it is fixed by `A` exactly when that covector is fixed by
`A^(-T)`.  Multiplication by the invertible matrix `A^T` identifies the
kernels of `A^(-T)-I` and `A^T-I`; transposition preserves rank, so this
kernel has the same dimension as `ker(A-I)`.  The point and line permutation
characters agree on every conjugacy class, hence the complex modules are
isomorphic.


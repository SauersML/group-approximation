---
rg: 2
id: boolean-violation-is-one-raw-radical-qubit-drop-proof
kind: route
title: Put each forbidden atom on one singular literal cycle
target: boolean-violation-is-one-raw-radical-qubit-drop
requires: []
---

For `a=(a_0,...,a_(k-1))`, let
`l_i(x)=[x_i=a_i]`, and form the `k` by `k` directed-cycle matrix

```text
C_a=I+sum_i l_i E_(i,i+1 mod k).                              (BRD10)
```

Only the identity permutation and the full directed cycle contribute to its
determinant, so

```text
det C_a=1+product_i l_i.                                      (BRD11)
```

If `x!=a`, some literal vanishes and `C_a(x)` is invertible.  At `x=a`, it is
`I` plus the cyclic permutation matrix.  Its left and right kernels are both
the one-dimensional span of the all-one vector.  Direct-sum `C_a` over
`a in F`.  At most one block is singular on any assignment, which proves
`(BRD2)--(BRD3)`.

The rank of the symmetrization in `(BRD4)` is twice the rank of `C_f`, proving
`(BRD5)`.  The standard normal form for a finite Heisenberg algebra with an
alternating form of rank `2r` is a direct sum of
`2^(2N-2r)` copies of `M_(2^r)(C)`.  Substitution of `r=N` and `r=N-1` gives
`(BRD6)--(BRD7)`.  The two embedded all-one kernel vectors give exactly the
words in `(BRD8)` and exhaust the radical.

The artifact constructs the matrices, verifies the rank and both raw kernel
vectors, and exhausts all predicates of arity at most three.

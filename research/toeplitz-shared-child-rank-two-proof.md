---
rg: 2
id: toeplitz-shared-child-rank-two-proof
kind: route
title: Iterate the constant packet block and row-reduce the star commutator form
target: toeplitz-schur-heads-share-child-but-have-rank-two
requires:
  - schur-packet-head-actuator-generates-over-tail
  - toeplitz-head-tail-unital-self-embedding
---

In `(SAT4)` of the head-actuator proof, `chi` is zero on `B_f^Q`.  Every
entry of `rho_0(g)` lies in `F_2`, and the unital endomorphism `sigma` fixes
`F_2`.  Iteration therefore proves `(TSR1)--(TSR2)`.  The faithful constant
block remains in every `B_n`, so each shifted map is again a faithful copy of
the same packet and the common selector words are literal equalities, not
merely conjugate words.

Same-root elementary transvections commute.  They also commute with the
disjoint constant packet block, proving the asserted relations among the
`p_n`.  In the ordered basis `(p_0,...,p_(N-1),q)`, the alternating matrix is

```text
Omega_N = [[0_(N by N), 1_N],
           [1_N^T,       0  ]].                              (TSR4)
```

Every one of the first `N` rows is equal, while the last row is nonzero and
not in their span.  Hence `(TSR4)` has rank two.  Equivalently,
`p_n+p_0`, for `n>0`, span an `(N-1)`-dimensional radical.  This proves
`(TSR3)` and the rank ceiling.

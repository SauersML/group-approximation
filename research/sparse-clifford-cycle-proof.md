---
rg: 2
id: sparse-clifford-cycle-proof
kind: route
title: Represent the cycle alternating form and use its vertex-cover inequality
target: sparse-clifford-cycles-refute-average-commutator-rounding
requires: []
---

Let `beta` be the alternating form on `F_2^L` whose matrix is the adjacency
matrix of the cycle.  The finite Heisenberg group associated with `beta` has
a finite-dimensional unitary representation in which the standard basis
reflections obey `(SCC1)` (quotient out the radical first if necessary).

There are `L` unordered cycle edges.  A commuting pair has commutator zero,
whereas an anticommuting reflection pair has commutator normalized-HS norm
two.  Counting both orientations proves `(SCC2)`.

Put `d_i=||A_i-B_i||_2`.  For every cycle edge `{i,j}`, bi-invariance and
the triangle inequality give

```text
2=||A_iA_j-A_jA_i||_2 <=2d_i+2d_j,
```

because `B_iB_j-B_jB_i=0`.  Summing over the cycle yields

```text
sum_i d_i >=L/2.
```

Jensen then gives `(1/L)sum_i d_i^2>=1/4`, proving `(SCC3)`.

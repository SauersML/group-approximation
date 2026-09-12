---
rg: 2
id: abelian-root-placement-birkhoff-polar-proof
kind: route
title: Match the doubly stochastic root-block masses and polar-round each matched block
target: abelian-root-average-placement-rounds-its-normalizer
requires: []
---

All traces on `M_(qm)` are normalized unless written `Tr`.
Write `||.||_F` for unnormalized Frobenius norm and `||.||_(S_1)`
for unnormalized trace norm, including on a matched block.
Unitarity makes `B` doubly stochastic. Conditional expectation gives

```text
E_A(VU_hV^*)=sum_x (sum_y B_(x,y)y(h))P_x.
```

Averaging its squared norm over `h` and using finite character
orthogonality yields `q^(-1)sum B_(x,y)^2`. Pythagoras proves `(ARP2)`.

Every doubly stochastic matrix is a convex combination of permutation
matrices. For completeness, its positive-entry bipartite support satisfies
Hall's condition: the total row mass of a set of rows equals its size and
is at most the number of its neighboring columns. Choose a supported
perfect matching, subtract the least entry on that matching, and normalize
the residual if it is nonzero. At least one positive entry disappears.
Iteration terminates and supplies the claimed convex decomposition.

Applying it to `B` itself shows that some permutation `pi` obeys

```text
sum_x B_(x,pi(x)) >= sum_(x,y)B_(x,y)^2.
```

Choose a unitary polar extension for each square matched block
`P_x V P_(pi(x))`. These extend across equal-dimensional kernels and
assemble into a unitary `W` normalizing `A`. Every singular value of a
compressed unitary lies in `[0,1]`, so its trace norm is at least its
squared Frobenius norm. Hence

```text
Re tr(W^*V)
 = (qm)^(-1)sum_x ||P_x V P_(pi(x))||_(S_1)
 >= q^(-1)sum_x B_(x,pi(x))
 >= 1-L(V).
```

Finally `||V-W||_2^2=2-2 Re tr(W^*V)<=2L(V)`, proving `(ARP1)`.

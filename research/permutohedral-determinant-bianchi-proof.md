---
rg: 2
id: permutohedral-determinant-bianchi-proof
kind: route
title: Multiply the face determinants and cancel every shared oriented edge
target: permutohedral-determinant-flux-is-bianchi-trivial
requires: []
---

Expand the left side of `(PDB2)` using `(PDB1)`.  The total exponent of the
edge phase `det(W_e)` is

```text
sum_f n_f epsilon_(f,e),
```

which is precisely the coefficient of `e` in the cellular boundary of
`sum_f n_f f`.  It vanishes because the chain is a cycle.  Every edge phase
therefore cancels with its inverse.

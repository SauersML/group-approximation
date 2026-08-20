---
rg: 2
id: ordered-bdd-compresses-predicate-rank-gate-proof
kind: route
title: Read the Boolean value as the unique live path and take a Schur complement
target: ordered-bdd-compresses-predicate-rank-gate
requires: []
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
---

For a fixed assignment, every decision node has precisely one outgoing edge
whose literal evaluates to one.  Reduction may skip variables but does not
alter this property.  Consequently the product of edge labels is one on the
unique evaluation path, and all other path products are zero.  After deleting
the false terminal, the source-to-true path sum is therefore exactly `f(x)`.

The adjacency matrix is nilpotent, so over `F_2`

```text
(I+N_f)^-1=I+N_f+N_f^2+... .                            (1)
```

Its source-to-true entry is the sum of all directed path products, hence
`f(x)`.  Since `U_f=I+N_f` is invertible, the block rank formula applied to
`(BDD1)` gives

```text
rank M_f=rank U_f+rank(e_s^T U_f^-1 e_t)=v+f(x).
```

The accompanying script constructs the reduced diagram by unique-table
memoization, verifies `(BDD2)` by Gaussian elimination on the full Boolean
cube, and exhausts every variable order for arity at most six.

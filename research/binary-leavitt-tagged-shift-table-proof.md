---
rg: 2
id: binary-leavitt-tagged-shift-table-proof
kind: route
title: Add a private orthogonal prefix column to every initial-address shift vertex
target: binary-leavitt-tagged-shift-table-has-centralizer-collisions
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
  - binary-leavitt-shift-graph-has-exact-marked-commutator-table
---

At a sufficiently deep common prefix level choose the `M` main pairs
`A_r,B_r` and one further prefix column `D_(ij)` for every vertex.  Dual
prefix orthogonality gives

```text
A_rB_s=delta_(rs)q,                 A_rD_(ij)=0.
```

For a vertex `(i,j)`, the Steinberg commutator relation gives

```text
[x_12(A_i),x_23(B_i+D_(ij))]
 =x_13(A_iB_i+A_iD_(ij))=x_13(q)=z.
```

If `(i,j)->(j,k)`, then `i!=j`, and the private tag is not a main column, so

```text
[x_12(A_j),x_23(B_i+D_(ij))]
 =x_13(A_jB_i+A_jD_(ij))=1.
```

The chromatic lower bound is the standard shift-graph argument already
proved by `binary-leavitt-shift-graph-has-exact-marked-commutator-table`.
For fixed `(i,j)`, all targets `(j,k)` have row `x_12(A_j)`.  Distinct
vertices have distinct column coefficients because the private dual-prefix
columns are linearly independent and disjoint from the main columns.  These
facts prove the two asserted centralizer-collision properties.

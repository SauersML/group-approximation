---
rg: 2
id: schur-flip-rank-is-residual-atomic-granularity-proof
kind: route
title: Read Pauli matrix units as equal-rank residual projections
target: schur-flip-rank-is-residual-atomic-granularity
requires:
  - schur-flip-cells-expose-residual-matrix-tape
---

The `r` independent cancellation pairs generate the full matrix algebra
`M_(2^r)(C)`.  Any unital finite-dimensional representation of this algebra
is a direct sum of its unique `2^r`-dimensional simple module.  Therefore its
ambient dimension is `L=2^r k`, and each diagonal matrix unit has rank `k`
and normalized trace `1/2^r`.  Conversely, if `L=2^r k`, the tensor
factorization `M_L=M_(2^r) tensor M_k` realizes the cells.  This proves
`(RAG1)`--`(RAG2)`.

In a diffuse finite factor, recursively bisect the identity into equivalent
orthogonal projections and choose partial isometries between the children.
At depth `r` these matrix units generate a unital `M_(2^r)` and all its
minimal projections have trace `2^(-r)`.  No positive atomic floor obstructs
the construction.


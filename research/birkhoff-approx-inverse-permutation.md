---
rg: 2
id: birkhoff-approx-inverse-permutation
kind: claim
title: A doubly stochastic approximate inverse is dimension-free close to a permutation
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

Let `B_N` be the Birkhoff polytope and use normalized Frobenius norm
`||A||_{2,N}^2 = N^{-1} sum_{i,j} |a_ij|^2`.

**Theorem.** If `P,Q in B_N` and `||PQ-I||_{2,N} <= eps`, then there is a
permutation matrix `S` with

```text
||P-S||_{2,N}^2 <= 1-(1-eps)^2 <= 2 eps.
```

The same statement holds for `Q`, because `||PQ||_{2,N} <= ||Q||_{2,N}` also
follows from `||P||_op <= 1`. The load-bearing point for Q3.4 is the conclusion:
once a bistochastic group-table model has an approximate inverse on the tested
inverse pairs, no additional high-dimensional Birkhoff integrality theorem is
needed.

The proof is elementary and dimension-free; it is recorded in
`birkhoff-approx-inverse-permutation-proof`.

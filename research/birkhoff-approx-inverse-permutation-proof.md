---
rg: 2
id: birkhoff-approx-inverse-permutation-proof
kind: route
title: Birkhoff decomposition and the normalized Frobenius norm force an extreme point
target: birkhoff-approx-inverse-permutation
requires: []
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

Every doubly stochastic matrix is a convex combination of permutation
matrices, hence has operator norm at most one. Therefore

```text
||PQ||_{2,N} <= ||P||_{2,N} ||Q||_op <= ||P||_{2,N},
```

while the triangle inequality gives `||PQ||_{2,N} >= 1-eps`. Thus
`||P||_{2,N} >= 1-eps`. The same argument with
`||PQ||_{2,N} <= ||P||_op ||Q||_{2,N}` gives `||Q||_{2,N} >= 1-eps`.

Choose a Birkhoff decomposition `P = sum_a lambda_a S_a`. With normalized HS
inner product,

```text
||P||_{2,N}^2 = sum_a lambda_a <P,S_a>,
```

so some permutation `S=S_a` satisfies `<P,S> >= ||P||_{2,N}^2`. Since
`||S||_{2,N}=1`,

```text
||P-S||_{2,N}^2
 = ||P||_{2,N}^2 + 1 - 2<P,S>
 <= 1-||P||_{2,N}^2
 <= 1-(1-eps)^2
 <= 2 eps.
```

Applying the same Birkhoff argument to `Q` proves its conclusion as well.

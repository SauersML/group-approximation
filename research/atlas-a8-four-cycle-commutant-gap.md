---
rg: 2
id: atlas-a8-four-cycle-commutant-gap
kind: claim
title: The minimal four-transvection cycle is a dimension-free A8 commutant test
artifacts:
  - experiments/atlas_a8_minimal_transvection_cycle.py
---

Let `lambda_k` be `k` copies of the left regular representation of
`A8 ~= GL_4(F2)` and let

```text
T={t01,t12,t23,t30}.
```

For every operator `X` with `||X||_op<=1`,

```text
dist_2(X,lambda_k(A8)')
 <= 17 ( sum_(t in T) ||[X,lambda_k(t)]||_2^2 )^(1/2). (A8-4COMM)
```

The constant is independent of `k`.  The finite audit proves that `T` has
directed Cayley diameter `17`, while
`atlas-a8-minimal-four-transvection-cycle` proves that four is the smallest
possible number of transvection test opcodes generating the full chart.

---
rg: 2
id: first-hit-carrier-contraction-ladder-proof
kind: route
title: Sum the persistent baseline against the finite trace budget
target: first-hit-carrier-contraction-ladder
requires: []
---

From `(FHC1)` and `(FHC2)`, for every `n<N`,

```text
eta q_0 <= eta q_n + eta Delta_n
            <= r_n + epsilon_n + eta Delta_n.
```

Sum over `n` and use `(FHC3)`.  This is `(FHC4)`.  Summing a fixed polynomial
over `0<=n<N` gives another fixed polynomial, which proves `(FHC5)`.

For projection carriers, `(FHC3)` follows from pairwise orthogonality:
`r_n=tau(R_n)` with `R_n R_m=0` for `n!=m` implies
`sum_n r_n=tau(sum_n R_n)<=tau(I)=1`.  The proof uses only normalized trace,
so its constant is independent of the ambient matrix dimension.

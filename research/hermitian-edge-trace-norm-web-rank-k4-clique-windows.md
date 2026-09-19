---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-clique-windows
kind: route
title: Cover C_n^4 by its n five-vertex clique windows and use c_5 >= 7.0857
target: hermitian-edge-trace-norm-web-rank-k4
requires:
  - hermitian-edge-trace-norm-clique-k5-margin
artifacts:
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k4_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k4_check.log
  - research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md
---

This is Steps 1–2 of `hermitian-edge-trace-norm-web-rank-large-k-clique-windows` with `m = 5`.

## Step 1. Windows

The `n` windows `{t, ..., t+4}` are cliques `K_5` of `C_n^4`, and each vertex lies in 5 of them.
The covering lemma (Step 1 there) and `hermitian-edge-trace-norm-clique-k5-margin` give
`||C||_1 >= (n/5) 7.0857`. Write `n = 5q + r` with `q = floor(n/5)`. This is at least
`sqrt3 (n - q)` iff

```text
(W4)     (7.0857 n)^2  >=  3 (4n + r)^2 .
```

## Step 2. Exact check

`eps_lo = 7.0857 - 4 (17320509/10^7) = 0.157496` is a lower bound for `7.0857 - 4 sqrt3`. For
`n >= N_0 = 44` we get `n eps_lo >= 4 sqrt3 >= sqrt3 r`, which is `(W4)`. `web_k4_check.py` tests
`(W4)` in exact rationals for `10 <= n <= 44`. It fails exactly for the twelve listed `n`
(`web_k4_check.log`). ∎

`n = 11` passes, which is the `C̄_11` argument again.

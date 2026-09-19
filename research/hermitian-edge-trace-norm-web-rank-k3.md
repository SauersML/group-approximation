---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k3
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_n^3 for every n >= 8 except n = 11
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k3-p6cube-windows.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k3_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k3_check.log
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/p6cube.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-large-k: that covers k = 3 only up to the exceptions n = 10, 11, 14, 15, 19, 23 (clique windows K_4); this removes all of them except n = 11, using windows P_6^3.
  hermitian-edge-trace-norm-web-rank-k2: that is k = 2 with windows P_6^2; this is k = 3 with windows P_6^3.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates; unreviewed, not Lean-verified;
route `hermitian-edge-trace-norm-web-rank-k3-p6cube-windows`).** Let `C_n^3` be the web on `Z_n`
with `i ~ j` iff the cyclic distance of `i` and `j` is `1`, `2` or `3`, and `n >= 8`, `n != 11`.
Every admissible `C` on `C_n^3` (Hermitian, zero diagonal, zero on non-edges, `|C_ij| >= 1` on
edges) has

```text
|| C ||_1  >=  sqrt3 (n - floor(n/4)) .
```

This is the Hermitian edge trace-norm inequality at the rank inequality `x(V) <= floor(n/4)` of the
web. For `n = 8` and `n = 9` it is part (b) of `hermitian-edge-trace-norm-web-rank-large-k`; for every
`n >= 9` except `n = 11` it follows from `c(P_6^3) >= 8.3139` by windows of six consecutive vertices.

**Still open: `n = 11`.** There the windows give `(11/6) 8.3139 = 15.242`, below `9 sqrt3 = 15.588`.
The same windows would close `n = 11` with `c(P_6^3) >= 54 sqrt3 / 11 = 8.50280`. The numerical
minimum `c(P_6^3) = 8.6413` (`pw.py`, not rigorous) is above that, so a certificate at the higher
target `8.5029` is the natural next step.

## Attempts

- 2026-09-18 (w7-078): `graphbb.py W12/1.2.3:0,1,2,3,4,5 8.3139 4.16 3` over the first free phase in
  two halves (`weblane.sh`, resumed from checkpoints across a container restart); both halves print
  `ALL CLOSED` (`p6cube.log`). `web_k3_check.log` does the exact arithmetic.

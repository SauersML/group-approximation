---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k3-n11
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_11^3, so the rank inequality of every web C_n^3 is settled
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k3-n11-p6cube-windows.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/p6cube_hi.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-large-k: that covers k = 3 by clique windows K_4 up to six exceptions, among them n = 11; this is exactly n = 11, by windows P_6^3.
  hermitian-edge-trace-norm-odd-antihole-c11: that is the antihole C_11^4 (the complement of C_11); this is the web C_11^3, a different graph on the same vertex set.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates; unreviewed, not Lean-verified;
route `hermitian-edge-trace-norm-web-rank-k3-n11-p6cube-windows`).** Let `C_11^3` be the web on
`Z_11` with `i ~ j` iff the cyclic distance of `i` and `j` is `1`, `2` or `3`. Its stability number
is `2`. Every admissible `C` on `C_11^3` (Hermitian, zero diagonal, zero on non-edges, `|C_ij| >= 1`
on edges) has

```text
|| C ||_1  >=  9 sqrt3  =  sqrt3 (11 - floor(11/4)) .
```

This is the Hermitian edge trace-norm inequality at the rank inequality `x(V) <= 2` of the web.

**Why it matters.** It was the last open web with `k = 3`. Lane w7-078's
`hermitian-edge-trace-norm-web-rank-k3` covers every `n >= 8` except `n = 11` (staged alongside,
from `c(P_6^3) >= 8.3139`). With it, `(R_{n,3})` holds for every `n >= 8`. The windows need
`c(P_6^3) >= 54 sqrt3/11 = 8.502795`, which is `1.6%` below the numerical minimum `8.6413` of
`c(P_6^3)`.

## Attempts

- 2026-09-18 (w8-078): proved by windows `P_6^3` and a robust exact-rational SDP branch-and-bound
  for `c(P_6^3) >= 8.5028`, route `hermitian-edge-trace-norm-web-rank-k3-n11-p6cube-windows`. The
  plain per-box-centre SDP of `graphbb.py` took `352400` boxes and `32201` s at `8.3139`. Box tests
  at `8.5028` put the plain method at `25-600` times that time, which is why the robust SDP was
  introduced.

---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-weighted-pendant
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_n^5 for 27 of the 35 open n, by the weighted window K_5 plus a pendant vertex
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k5-weighted-pendant-cover.md
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/pendant_windows.py
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/pendant_windows.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k5-to-k9: that proves C_n^5 outside 35 values of n by clique windows and Yudin certificates; this closes 27 of those 35 by a vertex-weighted six-vertex window.
  hermitian-edge-trace-norm-web-rank-k4-n13-n14: that proves the weighted bound c(H, w) >= 6.23539 and uses it on C_13^4 and C_14^4; this uses the same bound on C_n^5.
---

**ESTABLISHED (ordinary proof on top of the computer-assisted bound of
`hermitian-edge-trace-norm-web-rank-k4-n13-n14`, exact rational arithmetic; unreviewed, not
Lean-verified; route `hermitian-edge-trace-norm-web-rank-k5-weighted-pendant-cover`).**

**Theorem.** Let `C_n^5` be the web on `Z_n`, where `i ~ j` iff the cyclic distance of `i` and
`j` is in `1..5`. For

```text
n  in  {20, 21, 26, 27, 28, 32, 33, 34, 35, 39, 40, 41, 45, 46, 47, 51, 52, 53,
        58, 59, 64, 65, 70, 71, 77, 83, 89} ,
```

every admissible `C` on `C_n^5` satisfies `||C||_1 >= sqrt3 (n - floor(n/6))`. Admissible means
Hermitian, zero diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.

**The input.** `H` is `K_5` on `0..4` plus a vertex `5` joined only to `4`, and
`w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`. Then `c(H, w) >= 6.23539`, proved in
`hermitian-edge-trace-norm-web-rank-k4-n13-n14`. So the weighted density is
`c(H, w)/|w| >= 6.23539/4.2 = 1.484617 > 6 sqrt3/7 = 1.484615`.

**Why it matters.** With `hermitian-edge-trace-norm-web-rank-k5-to-k9`, only

```text
n  =  13, 14, 15, 16, 17, 22, 23, 29
```

remain open for `k = 5`. These need densities `sqrt3 (n - floor(n/6))/n` from `1.4656` (`n = 13`)
to `1.5283` (`n = 17`). `n = 13, 14` fail for a different reason: their needs `1.4656` and
`1.4846` are met, but no six vertices of `C_13^5` or `C_14^5` induce `H` (exhaustive check in
`pendant_windows.log`).

- The same window does nothing for the open `k = 6, 7` webs. There every need is at least
  `1.5242`, and `pendant_windows.log` lists them.

## Attempts

- 2026-09-19 (w11-078): proved by the `n` rotations of the window `{0, 1, 2, 3, 4, 9}`, which
  induces `H` in `C_n^5` for `n >= 15`, and the weighted covering lemma.

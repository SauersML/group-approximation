---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-weighted-pendant-cover
kind: route
title: Cover C_n^5 by the weighted rotations of the window {0,1,2,3,4,9} and use c(K_5 plus a pendant, w) >= 6.23539
target: hermitian-edge-trace-norm-web-rank-k5-weighted-pendant
requires:
  - hermitian-edge-trace-norm-web-rank-k4-n13-n14
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover.md
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/pendant_windows.py
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/pendant_windows.log
---

An ordinary proof on top of a computer-assisted bound. It is unreviewed and not Lean-verified.
Lane w11-078, 2026-09-19.

Notation is that of `hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover`: `H` is `K_5` on
`0..4` plus vertex `5` joined only to `4`, `w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, `|w| = 21/5`, and
`c(H, w)` is the minimum of `||C||_1` over Hermitian `C` on `H` with `|C_ij| >= sqrt(w_i w_j)` on
edges.

## Step 1. Inputs

- `c(H, w) >= 6.23539`: Step 3 of `hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover`.
  That bound is about the abstract graph `H` only; the web `C_14^4` there only names the graph.
- The weighted covering lemma, Step 1 of the same route: for diagonal `W_t >= 0` with
  `sum_t W_t <= I`, `||C||_1 >= sum_t ||W_t^(1/2) C W_t^(1/2)||_1`.

## Step 2. Windows in `C_n^5`, `n >= 15`

Let `U_t = {t, t+1, t+2, t+3, t+4, t+9}` (mod `n`).

- The six points are distinct, since `5 <= 9 <= n - 6`.
- The pairs of `t..t+4` are at distance at most `4`, so they are edges. The distance of `t+9` and
  `t+4` is `5`, an edge.
- The distance of `t+9` and `t+j`, `j = 0..3`, is `min(9 - j, n - 9 + j)`, which is at least 6 because
  `9 - j >= 6` and `n - 9 + j >= 6`. So these are non-edges.
- So `U_t` induces `H`, with `t + j` as `j` (`j <= 4`) and `t + 9` as `5`.

As in Step 2 of the `k = 4` route, put weight `w_j/|w|` on `t + j` and `w_5/|w|` on `t + 9`. Then
`sum_t W_t = I`, each weighted principal submatrix is feasible for `(H, w/|w|)`, and

```text
||C||_1  >=  n c(H, w) / |w|  >=  n x 6.23539 / 4.2 .
```

## Step 3. Arithmetic

`pendant_windows.py` checks, for each of the 35 open `n` of
`hermitian-edge-trace-norm-web-rank-k5-to-k9`:

- that `U_0` has six distinct points and induces exactly the edge set of `H`, and
- whether `(n x 6.23539 / (21/5))^2 >= 3 (n - floor(n/6))^2`, in exact rationals.

Both hold for the 27 values in the claim, and the inequality fails for `15, 16, 17, 22, 23, 29`.
For `n = 13, 14`, `U_0` fails the first check. The largest need among the 27 is at
`n = 21, 28, 35`, where `sqrt3 (n - floor(n/6))/n = 6 sqrt3/7`, and
`(14 x 6.23539)^2 = 7620.4973 >= 7620.48 = 432 (21/5)^2`.

## Step 4. Conclusion

For those 27 values of `n`, every admissible `C` on `C_n^5` has
`||C||_1 >= n c(H, w)/|w| >= sqrt3 (n - floor(n/6))`.

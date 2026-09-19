---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k3-p6cube-windows
kind: route
title: Cover C_n^3 by its n windows of six consecutive vertices and certify c(P_6^3) >= 8.3139 by SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k3
requires:
  - hermitian-edge-trace-norm-web-rank-large-k
artifacts:
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/weblane.sh
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/p6cube.log
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k3_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k3_check.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w7-078, 2026-09-18.

**Theorem.** For `n >= 8`, `n != 11`, every admissible `C` on `C_n^3` has
`||C||_1 >= sqrt3 (n - floor(n/4))`.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`. `P_6^3` is the cube of the
path on `0..5`, with `i ~ j` iff `1 <= |i - j| <= 3`; it has 12 edges.

## Step 0. n = 8

`n = 8` is part (b) of `hermitian-edge-trace-norm-web-rank-large-k` (clique windows `K_4`, whose
exception list for `k = 3` is `10, 11, 14, 15, 19, 23`). The steps below treat `n >= 9`.

## Step 1. Windows

Let `n >= 9` and `U_t = {t, ..., t+5}` (mod `n`). Two elements of `U_t` differ by `d in {1..5}`, with
cyclic distance `min(d, n-d)`. For `d <= 3` it is `d`, an edge. For `d in {4, 5}` it is at least `4`,
because `n - d >= 4` when `n >= 9`, so a non-edge. So `U_t` induces `P_6^3`. Each vertex lies in
exactly 6 windows, and the covering lemma (Lemma 1 of
`hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives `6 ||C||_1 >= n c(P_6^3)`.

## Step 2. Arithmetic

With `b = 8.3139 <= c(P_6^3)` it suffices that `(n b)^2 >= 108 (n - floor(n/4))^2`, an integer
inequality after scaling. `web_k3_check.py` checks it exactly for `9 <= n < 400`; it fails only at
`n = 11`. For the tail, `n - floor(n/4) <= 3(n+1)/4` and, with `s = 1.7321 > sqrt3`,
`n (b/6 - 3s/4) >= 3s/4` for every `n >= 16` (`b/6 - 3s/4 = 0.086575 > 0`), so
`n b/6 >= (3s/4)(n+1) > sqrt3 (n - floor(n/4))`.

## Step 3. `c(P_6^3) >= 8.3139`

`graphbb.py W12/1.2.3:0,1,2,3,4,5 8.3139 4.16 3 lo hi` builds `P_6^3` as the subgraph of `C_12^3`
induced on `0..5` and runs the exact SDP branch-and-bound of
`hermitian-edge-trace-norm-clique-inequality-k4-proof` (Steps 1-4) on the first free phase in
`[lo, hi]`. The two halves `[0, pi/4]` and `[pi/4, pi/2]` were run by `weblane.sh` (1200 s tries,
resumed from checkpoints) and both print `ALL CLOSED` (`p6cube.log`: 157089 + 195311 = 352400 boxes, 514413 SDP solves, smallest box-centre
value `8.667327`, 32201 s in all).

Why `[0, pi/2]` suffices: `graphbb.py` takes the BFS spanning tree from vertex `0`,
here `01, 02, 03, 14, 25`, makes the tree entries real by a diagonal unitary, and lists the free
edges in lexicographic order, so the first free phase is that of `12`. Two maps preserve the trace
norm, the zero pattern, the moduli and the reality of the tree. The map `C -> conj(C)` negates every
free phase. The map `C -> -E C E`, with `E = diag((-1)^depth(v))`, keeps the tree entries and
multiplies the free entry `uv` by `-(-1)^(depth u + depth v)`; for `12` (both of depth 1) that is a
shift by `pi`. As in Step 2 of `hermitian-edge-trace-norm-clique-inequality-k5-proof`, these bring
the phase of `12` into `[0, pi/2]` and leave the other free phases in `[0, 2 pi)`. ∎

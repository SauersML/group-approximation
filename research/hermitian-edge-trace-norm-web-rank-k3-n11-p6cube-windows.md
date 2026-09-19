---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k3-n11-p6cube-windows
kind: route
title: Cover C_11^3 by its eleven windows P_6^3 and certify c(P_6^3) >= 8.5028 by a robust exact-rational SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k3-n11
requires: []
artifacts:
  - research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md
  - research/hermitian-edge-trace-norm-clique-inequality-k4-proof.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/lane.sh
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/p6cube_hi.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w8-078, 2026-09-18.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`. `P_6^3` is the cube of the
path on `0..5`, with `i ~ j` iff `1 <= |i - j| <= 3`; it has 12 edges.

## Step 1. Windows

Let `U_t = {t, ..., t+5}` in `Z_11`. Two elements of `U_t` differ by `d in {1..5}`, with cyclic
distance `min(d, 11-d)`. That is `d` (an edge) for `d <= 3`, and `4` or `5` (a non-edge) for
`d = 4, 5`. So `U_t` induces `P_6^3`. Each vertex lies in exactly 6 of the 11 windows. The covering
lemma (Lemma 1 of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives
`6 ||C||_1 >= 11 c(P_6^3)`.

## Step 2. Arithmetic

Let `b` be the exact value of the double `8.5028`, i.e. `1196662715987683/2^47`. Then
`(11 b)^2 - 8748 = 0.01054... > 0`, so `11 b/6 > 9 sqrt3`. Hence `c(P_6^3) >= b` gives
`||C||_1 >= 9 sqrt3`. (`54 sqrt3/11 = 8.5027949`.)

## Step 3. `c(P_6^3) >= 8.5028`

`graphbb_r.py W12/1.2.3:0,1,2,3,4,5 8.5028 4.26 3 0 pi/2` builds `P_6^3` as the subgraph of
`C_12^3` induced on `0..5`. Its certificate is that of `graphbb.py`
(`experiments/hermitian-edge-trace-norm-webs-2026-09-18/`), which is
`hermitian-edge-trace-norm-clique-inequality-k4-proof` Steps 1-4 on a BFS spanning tree:

- Gauge the tree entries real and positive. If some `|K_ij| > T = 4.26`, then
  `||K||_1 >= 2 |K_ij| > 8.52`.
- Otherwise, for a Gaussian-rational Hermitian `Z` with `I - Z` and `I + Z` positive definite
  (checked by exact Fraction pivots), `||K||_1 >= tr(ZK)`. This is minimised over the moduli in
  `[1, T]` and the phase box edge by edge, with exact cosine ranges and outward rounding.
- A box is closed when that bound is `>= 8.5028`. Otherwise it is bisected.

The only change is how the candidate `Z` is found. `graphbb.py` takes the SDP dual optimum at the
box centre. `graphbb_r.py` solves one SDP that maximises a lower bound on `tr(ZK)` over the whole
phase box. Boxes of width `>= 3` are split without a solve. The candidate is then rounded and
checked exactly as before, so the certificate logic is unchanged.

`lane.sh` runs it in 1200 s tries, resumed from a checkpoint. `p6cube_hi.log` ends with `ALL CLOSED`:
40647 boxes, 78735 robust SDP solves,
4408 s in total over several resumed tries.

Why `[0, pi/2]` suffices. The BFS tree from vertex `0` is `01, 02, 03, 14, 25`. The free edges are
listed in lexicographic order, so the first free phase is that of `12`. The map
`C -> conj(C)` negates every free phase. The map `C -> -E C E`, with `E = diag((-1)^depth(v))`,
keeps the tree real and positive and shifts the phase of `12` (both ends of depth 1) by `pi`. Both
maps preserve the trace norm, the zero pattern and the moduli. A tree edge joins depths `d` and
`d+1`, so `-E C E` keeps its sign. On other free edges it shifts the phase by `0` or `pi`, and those
phases range over all of `[0, 2 pi)` anyway. The phase `theta` of `12` can be moved to `-theta`,
`theta + pi` and `pi - theta`, and one of these lies in `[0, pi/2]`. ∎

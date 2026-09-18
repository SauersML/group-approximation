---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k2-windows
kind: route
title: Cover C_n^2 by its n windows of six consecutive vertices and certify c(P_6^2) >= 4.5 sqrt3 by SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k2
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/p6sq.log
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/webfacet.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/webfacet.log
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/gmin.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/pw.py
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w7-078, 2026-09-18.

**Theorem.** For `n >= 8`, every admissible `C` on `C_n^2` has `||C||_1 >= sqrt3 (n - floor(n/3))`.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on the graph `F`. `P_6^2` is the
square of the path on six vertices `0..5`, with `i ~ j` iff `1 <= |i - j| <= 2`. It has 9 edges.

## Step 1. Windows

Let `U_t = {t, t+1, ..., t+5}` (mod `n`), `t in Z_n`. Two elements of `U_t` differ by
`d in {1, ..., 5}`, and their cyclic distance is `min(d, n - d)`. For `d <= 2` this is `d`, so they
are adjacent. For `d in {3, 4, 5}` it is at least `3`, because `n - d >= 3` when `n >= 8`, so they are
not adjacent. So `U_t` induces a copy of `P_6^2`.

Each vertex lies in exactly 6 windows. The covering lemma (Lemma 1 of
`hermitian-edge-trace-norm-odd-antihole-facets-by-size`: write `C = P - N` with `P, N >= 0`, so that
`||C_U||_1 <= sum_{i in U} |C|_ii`) gives

```text
6 || C ||_1  >=  sum_t || C_{U_t} ||_1  >=  n c(P_6^2) .
```

The last step holds because each principal submatrix `C_{U_t}` is admissible on `P_6^2`.

## Step 2. Arithmetic

Write `n = 3q + r` with `r in {0, 1, 2}`. Since `n >= 7`, `q >= 2 >= r`, so `4q >= 3q + r = n`, i.e.
`floor(n/3) >= n/4`. So `n - floor(n/3) <= 3n/4`. (The worst case, with equality, is `n = 8`.) It
therefore suffices that

```text
(n/6) c(P_6^2)  >=  sqrt3 (3n/4) ,   i.e.   c(P_6^2)  >=  (9/2) sqrt3  =  7.794229 .
```

## Step 3. `c(P_6^2) >= 7.7943`

`graphbb.py W12/1.2:0,1,2,3,4,5 7.7943 3.9 3` builds `P_6^2` as the subgraph of `C_12^2` induced on
`0..5`. It certifies `c(P_6^2) >= 7.7943` (`p6sq.log`: ALL CLOSED, 1770 boxes, 2572 SDP solves,
101 s, smallest box-centre value `8.1828`). Also `7.7943^2 = 60.75111... > 60.75 = (81/4) 3`.

`graphbb.py` is `experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py` with one
added graph family, `W<n>/<d1>.<d2>...:<vertices>`, the induced subgraph of a circulant. The
certificate scheme is unchanged (Steps 1–4 of `hermitian-edge-trace-norm-clique-inequality-k4-proof`).
- It gauges a BFS spanning tree real, which leaves 4 free phases, each over `[0, 2 pi]`.
- It closes moduli above `T = 3.9` by `2 x 2` compression (`2T >= 7.7943`).
- Every other box is closed by a Gaussian-rational `Z` with `-I < Z < I`, checked by exact
  `Fraction` pivots. The edge-separable bound `tr(ZC)` is minimised over the box with outward rounding.

The numerical value is `c(P_6^2) = 8.0653` (`pw.py`), so the margin is 3.5%. ∎

## Facets (not needed for the proof)

`webfacet.py` enumerates the maximum stable sets of `C_n^k` and computes the rank of their incidence
vectors. For `k = 2` and `6 <= n <= 19`, the rank is `n` (a facet) exactly when `3` does not divide
`n` (`webfacet.log`).

# Hermitian edge trace norm on webs (2026-09-18, lane w7-078)

This folder holds the scripts and logs for the webs `C_n^k`: vertices `Z_n`, with `i ~ j` iff the
cyclic distance of `i` and `j` is between `1` and `k`. The claim is `(**)` at the rank inequality,
`||C||_1 >= sqrt3 (n - floor(n/(k+1)))` for every admissible `C`. Admissible means Hermitian, zero
on the diagonal and on non-edges, and `|C_ij| >= 1` on edges.

## Files

| file | what it is |
|---|---|
| `graphbb.py` | `experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py` with one added graph family, `W<n>/<d1>.<d2>...:<v1>,...` (the subgraph induced on the listed vertices of the circulant on `Z_n` with distance set `{d1, d2, ...}`). The rigorous SDP branch-and-bound is unchanged. |
| `weblane.sh` | `weblane.sh GRAPH TARGET T TAG [LO HI]` runs `graphbb.py GRAPH TARGET T 3 LO HI` with the first free phase in `[LO, HI]` (default `[0, 2pi]`). It resumes from `ck_TAG.pkl` after each 1200 s try and appends to `TAG.log`. |
| `p6sq.log` | `graphbb.py W12/1.2:0,1,2,3,4,5 7.7943 3.9 3`: `c(P_6^2) >= 7.7943`. ALL CLOSED, 1770 boxes, 2572 solves, 101 s, smallest box-centre value 8.1828. |
| `webfacet.py`, `webfacet.log` | For `k = 2, 3, 4` and `2k+2 <= n <= 2k+15`: the stability number, the number of maximum stable sets and the rank of their incidence vectors. The rank inequality is a facet (rank `n`) exactly when `k+1` does not divide `n`, in this range. |
| `web_tail_check.py`, `web_tail_check.log` | Exact rational arithmetic for the clique-window route (`research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md`): positivity of `p(11 + x)` coefficient by coefficient, and the exact exception lists for `k = 3` and `5 <= k <= 29`. Runs in under a second. |
| `p6cube.log` | `weblane.sh W12/1.2.3:0,1,2,3,4,5 8.3139 4.16 p6cube_{a,b} LO HI` on `[0, pi/4]` and `[pi/4, pi/2]`: `c(P_6^3) >= 8.3139`. Both halves ALL CLOSED, 352400 boxes, 514413 solves, 32201 s, smallest box-centre value 8.6673. |
| `web_k3_check.py`, `web_k3_check.log` | Exact rational check for `k = 3` (`research/hermitian-edge-trace-norm-web-rank-k3-p6cube-windows.md`): with `c(P_6^3) >= 8.3139` the `P_6^3` windows prove the rank inequality for every `n >= 9` except `n = 11`. |
| `web_k4_check.py`, `web_k4_check.log` | Exact rational check for `k = 4` (`research/hermitian-edge-trace-norm-web-rank-k4-clique-windows.md`): with `c_5 >= 7.0857`, the clique windows `K_5` prove the rank inequality for every `n >= 10` except the listed twelve values. Runs in under a second. |
| `gmin.py`, `pw.py` | Numerical local minimisation of `||C||_1` (random restarts, BFGS then Nelder–Mead); not rigorous. `pw.py k w1,w2,... restarts` does the path powers `P_w^k`. |

## Results

- **`k = 2`, every `n >= 8`** (`research/hermitian-edge-trace-norm-web-rank-k2-windows.md`). The `n`
  windows of six consecutive vertices induce `P_6^2` and cover each vertex 6 times. Also
  `n - floor(n/3) <= 3n/4` for `n >= 7`. So `c(P_6^2) >= 4.5 sqrt3 = 7.79423` suffices, and
  `p6sq.log` certifies it.
- **`k >= 10`, every `n >= 2k+2`; and `k = 3`, `5 <= k <= 9` up to finite lists**
  (`research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md`). The `n` windows of
  `k + 1` consecutive vertices are cliques `K_{k+1}`. With the large-m bound
  `c_m >= 2 (c_00 m^2 - m F(1))/(m-1)`, and `c_4 >= 5.3887` for `k = 3`, they prove the rank
  inequality iff `n (c_m - sqrt3 (m-1)) >= sqrt3 (n mod m)`. `web_tail_check.log` has the lists.
  `k = 4` needs `c_5 > 4 sqrt3`.
- **`k = 3`, every `n >= 8` except `n = 11`** (`research/hermitian-edge-trace-norm-web-rank-k3.md`).
  Windows of six consecutive vertices induce `P_6^3`; `c(P_6^3) >= 8.3139` (`p6cube.log`) and
  `web_k3_check.log`. `n = 11` needs `c(P_6^3) >= 54 sqrt3/11 = 8.5028`.
- **`k = 4`, every `n >= 10` except `12, 13, 14, 17, 18, 19, 23, 24, 28, 29, 34, 39`**
  (`research/hermitian-edge-trace-norm-web-rank-k4.md`). The same `K_5` windows with
  `c_5 >= 7.0857` (`research/hermitian-edge-trace-norm-clique-k5-margin.md`); `web_k4_check.log`.

## Numerics (`pw.py`, not rigorous)

`c(P_w^k)/(sqrt3 w)` is the ratio that a window covering must beat. Its supremum over the webs
concerned is `3k/(3k+2)`, attained at `n = 3k+2`: for `k = 2` it is `0.75` and for `k = 3` it is
`0.818`.

| w | `k = 2`: c | ratio | `k = 3`: c | ratio |
|---|---|---|---|---|
| 5 | 6.4697 | 0.747 | 6.6524 | 0.768 |
| 6 | 8.0653 | 0.776 | 8.6413 | 0.832 |
| 7 | 9.5600 | 0.788 | 10.0966 | 0.833 |
| 8 | 11.3532 | 0.819 | 12.2322 | 0.883 |
| 9 | 12.9380 | 0.830 | 13.8545 | 0.889 |
| 10 | 14.3026 | 0.826 | 15.9363 | 0.920 |

Whole webs: `c(C_8^2) = 12.00`, `c(C_9^2) = 12.82`, `c(C_10^2) = 15.10`, `c(C_11^2) = 17.10`,
`c(C_12^2) = 17.86`, and `c(C_6^2) = 6.928 = 4 sqrt3` (the octahedron, where the bound is tight).

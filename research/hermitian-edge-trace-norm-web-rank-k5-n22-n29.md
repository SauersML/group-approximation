---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-n22-n29
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequalities of the webs C_22^5 and C_29^5, by a sharper certificate for the weighted window K_5 plus a pendant vertex
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k5-n22-n29-sharper-cover.md
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/k5p_62829.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k5-weighted-pendant: that uses c(H, w) >= 6.23539 and closes 27 values of n for k = 5; this certifies c(H, w) >= 6.2829 and closes n = 22 and n = 29, which that bound misses.
  hermitian-edge-trace-norm-web-rank-k4-n13-n14: that certifies c(H, w) >= 6.23539 for use on C_13^4 and C_14^4; this is a sharper certificate for the same H and w, used on C_22^5 and C_29^5.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates plus exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k5-n22-n29-sharper-cover`).**

**Theorem.** Let `C_n^5` be the web on `Z_n`, where `i ~ j` iff the cyclic distance of `i` and
`j` is in `1..5`. Every admissible `C` on `C_22^5` satisfies `||C||_1 >= 19 sqrt3`, and every
admissible `C` on `C_29^5` satisfies `||C||_1 >= 25 sqrt3`. These are `sqrt3 (n - floor(n/6))`.
Admissible means Hermitian, zero diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.

**The input.** `H` is `K_5` on `0..4` plus a vertex `5` joined only to `4`, and
`w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, `|w| = 21/5`. Then

```text
c(H, w)  >=  6.2829 ,
```

which is `0.72%` below the numerical minimum `6.32817`. So the weighted density is at least
`6.2829/4.2 = 1.495929`. The needs are `19 sqrt3/22 = 1.495904` and `25 sqrt3/29 = 1.493125`.

**Why it matters.** With `hermitian-edge-trace-norm-web-rank-k5-to-k9` and
`hermitian-edge-trace-norm-web-rank-k5-weighted-pendant`, only `n = 13, 14, 15, 16, 17, 23` remain
open for `k = 5`.

- For `n = 16, 17, 23` the needs `1.5155, 1.5283, 1.5061` are above the numerical density `1.5067`
  of `H` (at these weights; `wc3` scans of other weights stay at or below it), so this window
  cannot close them.
- For `n = 15` the need `1.5011` is only `0.37%` below `1.5067`. A certificate would have to come
  that close to the minimum.
- For `n = 13, 14`, no six vertices of `C_n^5` induce `H` (`pendant_windows.log`).

## Attempts

- 2026-09-19 (w11-078): proved by rerunning the `fastbbw.py` certificate of
  `hermitian-edge-trace-norm-web-rank-k4-n13-n14` at the higher target `6.2829`, then covering
  `C_n^5` by the rotations of the window `{0, 1, 2, 3, 4, 9}`.
- 2026-09-19 (w11-078): `K_6` plus a pendant vertex, weighted `(2/3 x5, 1, 1/8)`, has numerical
  density `1.5634`, which would close `k = 5, n = 16, 17` and `k = 6, n = 18, 25, 26, 27, 34`.
  - A 20-minute `fastbbw.py` pilot of its 10-phase certificate at target `6.865` covered only
    `1.3e-5` of the phase volume in 6000 solves.
  - The closed boxes have widths near `pi/4`, which would mean on the order of `10^7` boxes. That
    is out of reach for this solver.

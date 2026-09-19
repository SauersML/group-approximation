---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-n19
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_19^4, by six-vertex windows K_5 plus a vertex on a triangle
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-n19-g6-window-proof.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/g6s.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k4-three-exceptions: that proves every n >= 10 except 13, 14, 19 by five-vertex clique windows; this is n = 19, by the six-vertex window G_6.
  hermitian-edge-trace-norm-web-k4-small-window-limits: that shows which windows of at most six vertices could work at n = 13, 14, 19; this carries out the G_6 case at n = 19.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates plus exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k4-n19-g6-window-proof`).**

**Theorem.** Let `C_19^4` be the web on `Z_19`, where `i ~ j` iff the cyclic distance of `i` and
`j` is in `1..4`. Every admissible `C` on `C_19^4` satisfies

```text
||C||_1  >=  sqrt3 (19 - floor(19/5))  =  16 sqrt3  =  27.7128 .
```

Admissible means Hermitian, zero diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.

**The input.** Let `G_6` be the induced graph on `{0, 1, 2, 3, 4, 6}`: the clique `K_5` on `0..4`,
plus a vertex adjacent to `2, 3, 4`. Then `c(G_6) >= 8.7515`.

- Here `c(G_6)` is the minimum of `||C||_1` over admissible `C` on `G_6`.
- This is `0.67%` below the numerical minimum `8.8106`.

**Why it matters.** Together with `hermitian-edge-trace-norm-web-rank-k4-three-exceptions`, this
leaves only `n = 13, 14` of the rank inequalities of `C_n^4` open.

- `n = 13` needs `c(G_6) >= 8.7935`, a margin of `0.19%`.
  - A box closes only if its half-width is about the square root of the margin or less. So the
    same run would need roughly `(0.67/0.19)^4 ~ 150` times as many boxes, which is estimated,
    not measured.
- `n = 14` needs a window of seven or more vertices (`hermitian-edge-trace-norm-web-k4-small-window-limits`).

## Attempts

- 2026-09-19 (w10-078): proved by the 19 rotations of `G_6` and a symmetry-reduced branch-and-bound
  over the 8 free phases of `G_6` (`fastbb.py` of w9-078, unchanged).

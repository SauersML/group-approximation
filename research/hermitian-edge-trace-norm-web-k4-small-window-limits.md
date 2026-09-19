---
rg: 2
id: hermitian-edge-trace-norm-web-k4-small-window-limits
kind: claim
title: Window packings of the web C_n^4 at n = 13, 14, 19 - no window of at most six vertices works for n = 14, and for n = 13, 19 the only candidate is K_5 plus a vertex on a triangle
artifacts:
  - research/hermitian-edge-trace-norm-web-k4-small-window-limits-proof.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover6.log
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover7.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover7.log
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/member7.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/member7.log
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/g6min.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/g6min.log
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/frac.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/frac.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k4-three-exceptions: that proves the rank inequality of C_n^4 for every n >= 10 except 13, 14, 19, by five-vertex clique windows; this bounds what larger windows can do at the three exceptions.
  hermitian-edge-trace-norm-web-rank-large-k: that proves the rank inequality for k = 3 and k >= 5 with finitely many exceptions; this is only about k = 4 and only about window packings.
---

**ESTABLISHED for parts (a) and (b)** (an ordinary proof on explicit admissible matrices, checked
in floating point with margins of at least `0.010`; unreviewed, not Lean-verified; route
`hermitian-edge-trace-norm-web-k4-small-window-limits-proof`). Part (c) is numerics.

**Notation.**

- `C_n^4` is the web on `Z_n`, with `i ~ j` iff the cyclic distance of `i` and `j` is in `1..4`.
- For a graph `F`, `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`: Hermitian, zero
  diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.
- `R_n = sqrt3 (n - floor(n/5))`, which is `11 sqrt3`, `12 sqrt3` and `16 sqrt3` for
  `n = 13, 14, 19`.
- `G_6` is the induced graph on `{0, 1, 2, 3, 4, 6}`: the clique `K_5` on `0..4`, plus a vertex
  adjacent to `2, 3, 4`. Equivalently, it is `K_6` minus two edges at one vertex. It is `P_7^4`
  with the vertex `5` deleted, and it occurs in every `C_n^4` with `n >= 11`.

**The method.** Take vertex sets `W` of `C_n^4` and weights `y_W >= 0` with `sum_{W ni i} y_W <= 1`
at every vertex `i`. Then every admissible `C` satisfies

```text
||C||_1  >=  sum_W  y_W c(G[W]) .                                            (P)
```

This is how `hermitian-edge-trace-norm-web-rank-k4-three-exceptions` and
`hermitian-edge-trace-norm-web-rank-large-k` are proved. There, `W` runs over cliques of
consecutive vertices.

**Theorem.** Restrict (P) to sets with `|W| <= 6`.

- (a) For `n = 14`, the right side of (P) is below `R_14` for every choice of weights.
- (b) For `n = 13` and `n = 19`, the same holds for every choice of weights with `y_W = 0` whenever
  `G[W]` is isomorphic to `G_6`.
- So a six-vertex window proof of `n = 13` or `n = 19` must prove `c(G_6) >= 6 R_n / n`. That is
  `c(G_6) >= 8.7935` for `n = 13`, and `c(G_6) >= 8.7515` for `n = 19`. The numerical minimum is
  `c(G_6) ~ 8.8106` (4 runs of 10 starts agree to `3e-4`; `g6min.py`, `g6min.log`).
- It is enough, because the `n` rotations of `W = {0, 1, 2, 3, 4, 6}` with weight `1/6` form a
  valid packing.

**(c) Seven-vertex windows (numerics).** Upper bounds on `c` from `cover7.py` (2 starts each, so
local minima) are:

| window `W` | edges | free phases | `c` at most | occurs in `C_n^4` for `n` = | margin at 13 / 14 / 19 |
|---|---|---|---|---|---|
| `0..5, 7` | 17 | 11 | 10.700 | 13, 14, 19 | 4.3% / 3.0% / 4.8% |
| `0..6` (`P_7^4`) | 18 | 12 | 10.688 | 13, 14, 19 | 4.2% / 2.8% / 4.7% |
| `0..5, 8` | 16 | 10 | 10.494 | 13, 14, 19 | 2.3% / 1.0% / 2.8% |
| `0..4, 6, 8` | 15 | 9 | 10.424 | 13, 14, 19 | 1.6% / 0.3% / 2.1% |
| `0..4, 6, 9` | 15 | 9 | 10.452 | 13, 14 | 1.9% / 0.6% / - |
| `0, 1, 2, 3, 5, 7, 10` | 14 | 8 | 10.326 | 13, 14 | 0.7% / - / - |
| `0, 1, 2, 3, 5, 6, 8` | 14 | 8 | 10.268 | 13, 14, 19 | 0.1% / - / 0.6% |

- The margin is `c / (7 R_n / n) - 1`. The needed values `7 R_n / n` are `10.2590`, `10.3923` and
  `10.2100`.
- "Free phases" counts the edges outside a spanning tree. It measures the dimension of a
  branch-and-bound over phases.
- The window `0..5, 8` closes all three exceptions at once, with `10` phases instead of the `12` of
  `P_7^4`, if `c >= 10.3923` holds there.
- All `46` seven-vertex classes with at least `13` edges are in `cover7.log`, and `member7.log` lists the classes that occur in each of the three webs.

## Cost of a direct certificate on `P_7^4` (numerics)

- **Box bound.** The fixed-`Z` box bound of `fastbb.py` closes a box of `12` phases up to
  half-width about `0.7` when it uses the robust SDP (37 of 40 random boxes at `h = 0.7`, 8 of 40
  at `h = 0.9`), and up to about `0.5` with the sign `Z` alone. That is about `1.4e6` SDP boxes
  after symmetry, or 20 CPU-hours at the rate measured here.
- **Second-order bounds are weaker.** Three variants were tried (`so2.py`, `so2b.py`, `so2c.py`):
  a `Z` linear in the phase offsets, normalised by an eigenvalue bound; a Gram-matrix bound on the
  second-order term; and a rotation-type `Z = Z0 + D1 - Z0 D1^2 / 2`. All three certify less than
  the linear bound at every half-width tested. At one centre with `h = 0.7` they give `10.16` and
  `3.38`, against `10.99` for the linear bound and a true box minimum of `12.44`.
  - The curvature gain is only about `sum_e delta_e^2 / ||C||_1`. In `12` dimensions, the norm and
    cross-term remainders exceed it.
- **Freeing one edge** leaves at most `0.35%` margin (`freemin.py`, best `10.429`).

The cheaper windows in (c) are the better next step. For `n = 19`, `G_6` suffices and has been
certified: see `hermitian-edge-trace-norm-web-rank-k4-n19`.

## Attempts

- 2026-09-19 (w10-078): proved (a) and (b) with `cover.py` (91 window classes), and scanned the
  seven-vertex windows (c). Then certified `c(G_6) >= 8.7515` with `fastbb.py` (8 phases,
  `S_3 x Z_2` symmetry plus conjugation and negation, 353261 solves). That closes `n = 19`:
  `hermitian-edge-trace-norm-web-rank-k4-n19`. What remains is `n = 13`, which needs
  `c(G_6) >= 8.7935` (margin `0.19%`) or a seven-vertex window, and `n = 14`, which needs a window
  of seven or more vertices.
- 2026-09-19 (w11-078): the limits here are for unweighted windows. With vertex weights they fail.
  `K_5` plus a pendant vertex, `{0, 1, 2, 3, 4, 8}`, weighted `(3/4, 3/4, 3/4, 3/4, 1, 1/5)`, has
  density `1.5067`, and this closes `n = 13` and `n = 14`: `hermitian-edge-trace-norm-web-rank-k4-n13-n14`.
  - A correction to table (c): `c({0..5, 7}) <= 10.4799`, not `10.700`, which was a bad local
    minimum (`experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/w7min_7.log`).

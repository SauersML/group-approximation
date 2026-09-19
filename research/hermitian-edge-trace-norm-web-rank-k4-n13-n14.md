---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-n13-n14
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequalities of the webs C_13^4 and C_14^4, by vertex-weighted windows K_5 plus a pendant vertex
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover.md
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/k5p.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k4-three-exceptions: that proves every n >= 10 except 13, 14, 19 by unweighted five-vertex clique windows; this is n = 13, 14, by a vertex-weighted six-vertex window.
  hermitian-edge-trace-norm-web-rank-k4-n19: that is n = 19, by the unweighted window G_6; this is n = 13, 14, by the weighted window K_5 plus a pendant vertex.
  hermitian-edge-trace-norm-web-k4-small-window-limits: that shows no unweighted window of at most six vertices closes n = 14; this closes n = 14 with a six-vertex window by giving its vertices unequal weights.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates plus exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover`).**

**Theorem.** Let `C_n^4` be the web on `Z_n`, where `i ~ j` iff the cyclic distance of `i` and
`j` is in `1..4`. Every admissible `C` on `C_14^4` satisfies

```text
||C||_1  >=  sqrt3 (14 - floor(14/5))  =  12 sqrt3  =  20.7846 ,
```

and every admissible `C` on `C_13^4` satisfies `||C||_1 >= 11 sqrt3 = 19.0526`. Admissible means
Hermitian, zero diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.

**The inputs.**

- *Weighted covering lemma.* If `C` is Hermitian and `W_1, ..., W_m` are diagonal, `W_t >= 0`,
  with `sum_t W_t <= I`, then `||C||_1 >= sum_t ||W_t^(1/2) C W_t^(1/2)||_1`. With `W_t = I_{U_t}`
  this is the covering lemma of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`.
- *The window.* `H` is the clique `K_5` on `0..4` plus a pendant vertex `5` joined to `4`; it is
  the subgraph of `C_n^4` induced on `{0, 1, 2, 3, 4, 8}` for `n = 13` and `n = 14`. With weights
  `w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, `|w| = 21/5`, the weighted value satisfies

  ```text
  c(H, w)  >=  6.23539 ,
  ```

  where `c(H, w)` is the minimum of `||C||_1` over Hermitian `C` on `H` with `|C_ij| >= sqrt(w_i w_j)`
  on edges. This is `1.47%` below the numerical minimum `6.32817`.

Then `||C||_1 >= n c(H, w)/|w|`, and `14 x 6.23539 / 4.2 > 12 sqrt3`, `13 x 6.23539 / 4.2 > 11 sqrt3`.

**Why it matters.** With `hermitian-edge-trace-norm-web-rank-k4-three-exceptions` and
`hermitian-edge-trace-norm-web-rank-k4-n19`, the rank inequality of `C_n^4` now holds for every
`n >= 10`, so `k = 4` joins `hermitian-edge-trace-norm-web-rank-large-k` with no exceptions.

- `hermitian-edge-trace-norm-web-k4-small-window-limits` shows that no unweighted window of at most
  six vertices closes `n = 14`. Unequal weights beat that bound: the unweighted density of `H` is
  far too low, but the weighted density `c(H, w)/|w| = 1.5067` exceeds the `1.4846` that `n = 14`
  needs.
- The brief's unweighted route, `c({0..5, 8}) >= 6 sqrt3` over 10 phases, was estimated at about
  `4e7` solves from a pilot; this route took the solves recorded in `k5p.log`.

## Attempts

- 2026-09-19 (w11-078): proved by the weighted covering lemma on the `n` rotations of the window
  `{0, 1, 2, 3, 4, 8}` with weights `(3/4, 3/4, 3/4, 3/4, 1, 1/5)`, and `c(H, w) >= 6.23539` by
  `fastbbw.py`, a vertex-weighted version of w9-078's `fastbb.py`, over 6 phases reduced by `S_4`.

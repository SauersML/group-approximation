---
rg: 2
id: hermitian-edge-trace-norm-web-rank-large-k
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of every web C_n^k with k >= 10, and of all but finitely many C_n^k for k = 3 and 5 <= k <= 9
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_tail_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_tail_check.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k2: that is the webs C_n^2, by six-vertex windows and a branch-and-bound certificate; this is k = 3 and k >= 5, by clique windows and the clique bounds already proved.
  hermitian-edge-trace-norm-other-stab-facets-non-antihole: that is every non-clique, non-hole, non-antihole facet; this is only the rank inequalities of webs.
  hermitian-edge-trace-norm-odd-antihole-facets: that is the antiholes C_{2k+3}^k for every k; this contains the antiholes with k >= 10 (n >= 23), which are already proved there by the same clique covering, and adds every other n.
---

**ESTABLISHED (ordinary proof on top of certified clique bounds; the arithmetic is checked in exact
rational arithmetic; unreviewed, not Lean-verified; route
`hermitian-edge-trace-norm-web-rank-large-k-clique-windows`).**

For `k >= 1` and `n >= 2k + 2`, the web `C_n^k` has vertices `Z_n`, with `i ~ j` iff the cyclic
distance of `i` and `j` is in `1..k`. Its stability number is `floor(n/(k+1))`. An admissible `C`
on a graph is Hermitian, zero on the diagonal and on non-edges, with `|C_ij| >= 1` on edges.

**Theorem.** Write `m = k + 1`. Every admissible `C` on `C_n^k` satisfies

```text
|| C ||_1  >=  sqrt3 ( n - floor(n/m) )                                   (R_{n,k})
```

in each of these cases:

- (a) `k >= 10`, every `n >= 2k + 2`;
- (b) `k = 3`, every `n >= 8` except `n = 10, 11, 14, 15, 19, 23`;
- (c) `k = 6`, every `n >= 14` except `16-20, 24-27, 32-34, 40, 41, 48`;
- (d) `k = 7`, every `n >= 16` except `20-23, 30, 31, 39`;
- (e) `k = 8`, every `n >= 18` except `24, 25, 26`;
- (f) `k = 9`, every `n >= 20` except `n = 29`;
- (g) `k = 5`, every `n >= 12` except 62 values, the largest `143` (listed in `web_tail_check.log`).

For `n = 2k + 1` the web is the clique `K_{2k+1}`, and `(R_{n,k})` is the clique inequality,
which is `hermitian-edge-trace-norm-clique-inequality`. The case `k = 4` is not covered: it needs
`c(K_5) > 4 sqrt3`, which is the high-target `K_5` run of `hermitian-edge-trace-norm-odd-antihole-c11`.

**Why it matters.** `(R_{n,k})` is `(**)` at the rank inequality `x(V) <= floor(n/(k+1))` of
`STAB(C_n^k)`. Webs are the standard family of rank facets beyond holes and antiholes (Trotter
1975). `webfacet.log` computes, for `k = 2, 3, 4` and `2k+2 <= n <= 2k+15`, that the rank
inequality is a full-support facet exactly when `(k+1)` does not divide `n`. The theorem does not depend on which
of them are facets. Together with `hermitian-edge-trace-norm-web-rank-k2`, it settles `(**)` on the
rank inequalities of all webs with `k >= 2` except `k = 4` and the finitely many listed pairs.
(`k = 1` is the odd holes.)

**Proof in three lines.** The `n` windows `{t, ..., t + k}` are cliques `K_m` and cover every vertex
`m` times. So `||C||_1 >= (n/m) c_m`, where `c_m` is the minimum trace norm on `K_m`. With
`n = q m + r`, this is at least `sqrt3 (n - q)` iff `n eps_m >= sqrt3 r`, where
`eps_m = c_m - sqrt3 (m-1)`. The large-m proof gives `c_m >= 2 (c_00 m^2 - m F(1))/(m-1)`. For
`m >= 11` this makes `eps_m >= sqrt3 (m-1)/(3m-1)`, which is enough for every `n >= 2m`. For the
listed small `k`, a finite exact check finds the exceptions.

**Numerics** (not part of the proof). The exceptions are genuine limits of the clique covering, not
of `(R_{n,k})`. For example, for `k = 3` local minimisation (`gmin.py`, 20 restarts) gives
`c(C_10^3) = 16.598` and `c(C_11^3) = 18.429`, which are `1.198` and `1.182` times the bound. The windows `P_w^k` of more than `k + 1` vertices are the natural
next tool for them (`hermitian-edge-trace-norm-web-rank-k2` uses `P_6^2`).

## Attempts

- 2026-09-18 (w7-078): proved by clique windows, route
  `hermitian-edge-trace-norm-web-rank-large-k-clique-windows`. A certificate `c(P_6^3) >= 8.3139`
  was running at the time of writing. It would give `k = 3` for every `n >= 9` except `n = 11`, and
  so close the `k = 3` exceptions other than `n = 11`.
- 2026-09-18 (w7-078): `k = 4` is now covered, up to twelve values of `n`, by
  `hermitian-edge-trace-norm-web-rank-k4` (the same `K_5` windows with
  `hermitian-edge-trace-norm-clique-k5-margin`). The `P_6^3` run finished: `c(P_6^3) >= 8.3139`,
  and `hermitian-edge-trace-norm-web-rank-k3` removes every `k = 3` exception except `n = 11`.
- 2026-09-18 (w8-078): a Yudin certificate tuned to each clique size `m = 6..10` (five verified
  `F`, degree 6 or 10) raises the certified `eps_m` to `0.0967, 0.2628, 0.4275, 0.6197, 0.8222`.
  `hermitian-edge-trace-norm-web-rank-k5-to-k9` uses them to settle `k = 8, 9` for every `n`. It also
  shortens the lists to 35 values for `k = 5` (the largest `89`), `17-20, 25-27, 34` for `k = 6`, and
  `22, 23` for `k = 7`. The LP value is flat in the degree, so the remaining `n` need windows of more
  than `k + 1` vertices or a different bound on `c_m`.
- 2026-09-18 (w8-078): a robust exact-rational SDP branch-and-bound
  (`experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py`) proves
  `c(P_6^3) >= 8.5028 > 54 sqrt3/11`. `hermitian-edge-trace-norm-web-rank-k3-n11` then closes
  `n = 11`, so `(R_{n,3})` holds for every `n >= 8`. The same code proves `c(K_5) >= 7.168`, and
  `hermitian-edge-trace-norm-web-rank-k4-six-exceptions` reduces `k = 4` to `n = 12, 13, 14, 18, 19, 24`.
  Next: `c(K_5) >= 7.2169` would close `12, 18, 24`, and `c(P_7^4) >= 6 sqrt3` would close all six.
- 2026-09-18 (w9-078): `experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/fastbb.py` proves
  `c(K_5) >= 7.2169` in 20027 solves. It adds two things to `graphbb_r.py`: a pinching cut on large
  moduli (`2T + 2 sqrt3`), and a fundamental domain for `S_5 x conj x neg` on the triangle phases.
  With it, `hermitian-edge-trace-norm-web-rank-k4-three-exceptions` reduces `k = 4` to
  `n = 13, 14, 19`. Five-vertex windows cannot do better, even at `c_5 = 5 + sqrt5`.
  - Sampled costs for the next windows: `c(P_7^4) >= 6 sqrt3` is about `1.1e8` boxes, and
    `c(K_6) >= 9.17` (for `k = 5`) is about `5.5e6` boxes.
  - Obstruction: a fixed-`Z` certificate closes an arc only up to half-width
    `arccos(target/||C||_1) ~ 0.7`.
  - Next: a box bound that is not linear in `K`, for instance a second-order (`Z` plus a correction
    in the phases) or a sum-of-squares certificate in `cos`/`sin` of the phases. Alternatively,
    a proof of `c_6 >= 9.17` or `c(P_7^4) >= 6 sqrt3` from smaller pieces by pinching.
- 2026-09-19 (w10-078): `k = 4`, `n = 19` is proved: `hermitian-edge-trace-norm-web-rank-k4-n19`,
  by the 19 rotations of the six-vertex window `G_6 = K_5` plus a vertex on a triangle, and
  `c(G_6) >= 8.7515` by branch-and-bound. Only `n = 13, 14` of `k = 4` remain.
  - `hermitian-edge-trace-norm-web-k4-small-window-limits`: among windows of at most six vertices,
    only `G_6` can close `n = 13`, which needs `c(G_6) >= 8.7935` against a numerical value of
    `8.8106`. None can close `n = 14`.
  - Seven-vertex windows with fewer phases than `P_7^4` are tabulated there. The best is
    `{0..5, 8}`, with 10 phases and a 1% margin at `n = 14`.
  - Second-order box bounds on `P_7^4` are weaker than the linear one.

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

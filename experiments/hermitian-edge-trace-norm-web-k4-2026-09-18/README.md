# Symmetry-reduced robust-SDP branch-and-bound: `c(K_5) >= 7.2169` (lane w9-078, 2026-09-18)

Supports `research/hermitian-edge-trace-norm-web-rank-k4-three-exceptions-windows.md`.

## fastbb.py

`fastbb.py GRAPH TARGET T A_LO A_HI checkpoint.pkl` (env `ROOT`, `FIRST`, `SYM`, `CKEVERY`) is
`experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py` made cheaper.

**The certificate is that of `graphbb.py` / `graphbb_r.py`.** Gauge the BFS-tree entries real and
positive; the other entries `K_ij = t_ij e^{i th_ij}` carry the free phases. On a box of free phases
with all moduli in `[1, T]`, a Gaussian-rational Hermitian `Z` with `I - Z` and `I + Z` positive
definite (exact Fraction pivots, `check_exact`) gives `||K||_1 >= tr(ZK)`. `box_bound` minimises
`tr(ZK)` edge by edge over the moduli and the phase arc, with exact cosine ranges and outward
padding. A box is closed only when `box_bound >= TARGET` for an exactly checked rational `Z`.
`round_Z`, `pd_exact`, `check_exact`, `cos_min`, `edge_terms` and `box_bound` are the same
arithmetic as in `graphbb_r.py`.

Two changes affect what is proved. Both are proved here.

1. **Modulus cut by pinching.** Suppose `|K_ij| = t > T` on some edge `ij`. Pinching into `{i, j}`
   and the other vertices gives `||K||_1 >= 2t + ||K_R||_1`, where `R` is the vertex set other than
   `{i, j}`. Pinching `K_R` further into vertex-disjoint edges and triangles gives
   `||K_R||_1 >= 2 (#edges) + 2 sqrt3 (#triangles)`.
   - An edge block is `[[0, a], [conj a, 0]]` with trace norm `2|a| >= 2`.
   - A triangle block is a `3 x 3` Hermitian matrix with zero diagonal and entries of modulus at
     least `1`. Its eigenvalues sum to `0` and `sum lambda^2 = ||.||_F^2 >= 6`. The positive
     eigenvalues and the moduli of the negative ones each sum to `s/2`, where `s` is the trace norm.
     So `sum lambda^2 <= 2 (s/2)^2 = s^2/2`, which gives `s >= sqrt12 = 2 sqrt3`.
   - `MCUT` is the minimum over edges of the best such packing of `R`, computed by exhaustive
     recursion. The triangle value is rounded down by a factor `1 - 1e-12`.
   - The script asserts `2T + MCUT >= TARGET`. For `K_5`, `R` is a triangle and `MCUT = 2 sqrt3`, so
     `T = 1.877` is valid for `TARGET = 7.2169`. Before, the cut was `2T >= TARGET`, which needed
     `T = 3.6`.
2. **Symmetry domain** (env `SYM`). A box is dropped without a certificate if, on the whole box,
   `u(q) < u(p)` for one condition `p < q`.
   - `u(x) = dist(x, pi Z)`.
   - A term is a signed sum of free phases, and interval arithmetic gives its exact range.
   - Which conditions are valid is argued below for `K_5`.

The other changes only affect the search. They cannot close a box that `box_bound` does not close.

- Candidates are tried in order: the parent's rational `Z`, the rounded `sign(C(centre))`, and the
  robust SDP of `graphbb_r.py`. The SDP is now solved by Clarabel directly (class `RobustSDP`),
  which is 2.6 times faster than through cvxpy.
- Arcs of length `>= pi` are allowed. The robust SDP then sets `Z_ji = 0` on that edge.
- The box is bisected in the phase whose arc costs `box_bound` the most for `sign(C(centre))`.
- A checkpoint is written every 1000 solves. `run.sh TAG GRAPH TARGET T A_LO A_HI` repeats
  `nice -n 10 timeout 1200 fastbb.py ...`, resuming from `TAG.pkl`, until `ALL CLOSED` or `FAIL`.
- A centre with `||C(centre)||_1 < TARGET` (moduli `1`, an admissible matrix) stops the run with
  `FAIL`: then the target is false.

## The symmetry domain for `K_5`

The star tree at `0` makes `K_0i > 0`. The free phases are those of `12, 13, 14, 23, 24, 34`, in
that order, and the first lies in `[A_LO, A_HI]`. The triangle phase
`phi(abc) = arg(K_ab K_bc K_ca)` is gauge invariant.

- For a triangle through `0`, `phi(0ij) = th_ij`.
- Otherwise, `phi(ijk) = th_ij + th_jk - th_ik`.

These operations preserve admissibility and the trace norm: vertex permutations (`S_5`), `K -> conj K`
and `K -> -K`, each followed by regauging. They permute the ten triangle phases, up to sign and up
to adding `pi` (`-K` adds `pi` to all of them). So they permute the ten values `u(phi(T))`.

```text
SYM_K5 = 1.2<1.3,1.4,2.3,2.4,3.4,1.2+2.3-1.3,1.2+2.4-1.4,1.3+3.4-1.4,2.3+3.4-2.4;1.3<2.3,1.2+2.3-1.3,1.4,2.4,1.2+2.4-1.4
```

The domain `D` is `th_12 in [0, pi/2]`, together with two conditions:

- (A) `u(phi(012))` is at most `u(phi(T))` for all ten triangles `T`;
- (B) `u(phi(013))` is at most `u(phi(T))` for the six triangles
  `T = {a, b, x}` with `{a, b}` in `{0, 1, 2}` and `x` in `{3, 4}`.

**Every admissible `K` has an image in `D`.**

1. `S_5` is transitive on triangles. So a permutation moves a triangle of least `u` to `012`, which gives (A).
2. The setwise stabiliser `S_{0,1,2} x S_{3,4}` of `012` preserves (A). It is transitive on the six
   triangles of (B), so one of its elements gives (B).
3. `conj` and `-K` keep every `u`. They move `th_12 = phi(012)` to `-th_12` and `th_12 + pi`, and one of
   `+-th_12`, `+-th_12 + pi` lies in `[0, pi/2]`.

So proving `||K||_1 >= TARGET` on `D` proves it for every admissible `K`.

`symtest.py` is an independent numerical check. For each of 3000 random admissible `K` it searches
`S_5 x conj x neg` for an image in `D`. `symtest.log` reports that every `K` has one.

## Runs (`TARGET = 7.2169`, `T = 1.877`, `SYM = SYM_K5`)

- `k5a.log` (`th_12 in [0, pi/4]`): `ALL CLOSED`. There are 5665 closed boxes and 549 dropped by
  symmetry, in 11160 solves and 607 s. The smallest half-width is `0.065` and the least centre
  value is `7.2688`.
- `k5b.log` (`th_12 in [pi/4, pi/2]`): `ALL CLOSED`. There are 3966 closed boxes and 1424 dropped,
  in 8867 solves and 535 s. The least centre value is `7.3061`.
- Together, `||K||_1 >= 7.2169` for every admissible `K` on `K_5`, so `c(K_5) >= 7.2169`. The
  bound is the double `8125507037692533/2^50 >= 7.2169`, and `2T + 2 sqrt3 (1 - 1e-12) = 7.2181`.
  The numerical minimum is `5 + sqrt5 = 7.2361`.
- `control_7.24.log`: the same run at `TARGET = 7.24`, which is above `7.2361`, stops with `FAIL`
  at an admissible centre with `||C||_1 = 7.23957`, inside `D`. So the domain and the search do see
  the minimum.
- `web_clique_lists_k4.log`: the exact clique-window list with `L_5 = 7.2169`, from
  `experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.py`. The
  exceptions are `n = 13, 14, 19`.

For comparison, `c(K_5) >= 7.168` took 45264 solves with `graphbb_r.py`
(`experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/k5_*.log`). With `fastbb.py` it takes
14320 solves: the same target, with `T = 1.853` and `SYM_K5`.

## Cost of the next windows (sampling, not run)

For 30 random centres (20 for `K_6`), take the largest half-width in the ladder
`1.2, 0.9, 0.7, 0.5, ...` at which a cube around the centre closes with one robust solve.

| window | target | typical half-width | estimated boxes, no symmetry |
|---|---|---|---|
| `P_7^4`, 12 phases | `10.3924` (`T = 2.465`, `MCUT = 2 + 2 sqrt3`) | `0.7` at 27 centres, `0.5` at 3 | `1.1e8` |
| `K_6`, 10 phases | `9.17` (`T = 2.585`, `MCUT = 4`) | mostly `0.7` | `5.5e6` |

The `P_7^4` target would close `n = 13, 14, 19`. The `K_6` target would close the 35 values for `k = 5`.

- The limit is the fixed-`Z` bound itself. On an arc of half-width `h` it keeps only `cos h` of each
  edge term. So a generic box needs `h <= arccos(TARGET / ||C||_1) ~ 0.7`.
- `P_7^4` has automorphism group `S_3 x Z_2`: it permutes `{2, 3, 4}` and reverses the complement
  path `5-0-6-1`. With `conj` and `-K`, that is at most a factor 48.
- For `K_5` the domain gave only a factor of about 3, because boxes near the minimum straddle its
  boundary.

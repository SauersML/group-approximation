---
rg: 2
id: zn-rips-contractible-at-every-scale-r-ge-n
kind: claim
title: "Zaremsky's conjecture: the Rips complex of Z^n in the l^1 metric is contractible at every scale r ≥ n"
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is Zaremsky's Problem 4.3, contractibility for all large enough scales, answered by Virk; this is the sharp form, every scale r ≥ n
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this asks for every r ≥ n
---

For every `n ≥ 1` and every integer `r ≥ n`, the Vietoris–Rips complex `VR(Z^n, d_1; r)` is contractible. A finite
set spans a simplex iff its `l^1` diameter is at most `r`.

Here `d_1` is the standard word metric. Large-scale contractibility is Virk's theorem (`rips-complexes-of-integer-lattices-are-contractible`).
This claim asks for the sharp threshold.

Status on main, by dimension:
- `n ≤ 6`: every `r ≥ n`. This is Gupta–Sarkar–Shukla together with `z6-rips-contractible-at-scales-6-to-9`.
- `n = 7`: every `r ≥ n`. The sources are:
  - `z7-rips-contractible-at-scales-7-and-8`;
  - `z7-rips-contractible-at-scale-9`;
  - `z7-rips-contractible-at-scale-10`;
  - `z7-rips-contractible-at-scales-11-13-15-17`;
  - `z7-rips-contractible-at-scales-12-14-16-and-18-to-54`;
  - `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54`;
  - Zaremsky's bound `r ≥ 55`.
- `n = 8`: every `r ≥ 37` and every even `r ≥ 20`. The sources are
  `z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70` and `z8-rips-contractible-at-even-scales-38-to-70`,
  with the published bound `r ≥ 71`. Open: `8 ≤ r ≤ 19` and odd `21 ≤ r ≤ 35`.
  At `r = 8`, the lifted reduction of `z7-rips-contractible-at-scale-10-proof` admits no domination-only
  certificate (`z8-rips-lifted-domination-certificates-fail-at-scale-8`), so that scale needs link collapses or a
  new move.
- General `n`, sufficient criteria on the partitions of `r`: `zn-rips-sphere-balanced-dominator-criterion` and
  `zn-rips-slack-sphere-criterion`.

## Attempts

- **w3-103, partition criteria.** The balanced-dominator and slack-one sphere criteria handle each scale where every
  unbalanced partition of `r` into at most `n` parts has exactly `n` parts. They stall when some unbalanced partition
  has fewer than `n` parts: the stuck sphere points then have a zero coordinate. For `n = 7` this happens at
  `r = 10, 11, 13, 15, 17`.
- **w5-103, lifted interleaved certificates.** The reduction is in `z7-rips-contractible-at-scale-10-proof`.
  - *Lift.* A peeling link lives in the dimension `k` of its last positive box side, so `e_k` is always available
    as a dominator direction. There is one certificate per `k ≤ n`, and each ends at `{e_k}`.
  - *Interleaving.* Norm `r − 1, …, 2` points are deleted against the remaining sphere.
  - *Cone collapse.* A link is collapsed to a cone with the moves `hull(0, u, b, e_k)`.

  Result: `(7, 10)` is closed.
  - In exploratory runs without the lift, the greedy stalls at `(6,6)`, `(7,7)`, `(7,8)` and `(7,10)`.
  - Point-level certificates grow quickly: `|Lmax_7|` is 216,952 at `r = 10` and 397,727 at `r = 11`, and far larger
    at `(7,17)` and at `n = 8`. The remaining scales need either staged runs or a partition-level version of the lifted
    moves.
- **w5-103, layered orbits and self-blocking sets.**
  - *n = 7 closed.* Orbit-level (D) certificates, with Lemmas O and P of
    `z7-rips-contractible-at-scales-11-13-15-17-proof`, close `r = 11, 13, 15, 17`.
  - *Orbit moves fail at n = 8.* At `(8, 8)` orbit moves stall. A hybrid that falls back to point moves on the
    deferred orbits also stalls after 62,442 verified moves, with 70,422 points left
    (`experiments/zn-rips-lifted-domination-core-2026-09-18/`).
  - *Obstruction.* Every (D)-only certificate fails at `(8, 8)`. A 16,114-point self-blocking set blocks every
    (D) move into it, whatever the order (`z8-rips-lifted-domination-certificates-fail-at-scale-8`). The same test
    finds self-blocking sets at `(6, 6)`, `(7, 7)`, `(7, 8)` and `(7, 9)`, all of them closed on main by other means,
    but none at `(6, 7)`–`(6, 9)`.
  - *Next.* Link-collapse (K) certificates at `(8, 8)`, aimed at the self-blocking set, and a scan at `(8, r ≥ 9)`
    for the scales where the greatest self-blocking set is `{e_8}`.
- **w6-103, link-collapse certificates.** `(8, 8)` is closed: `z8-rips-contractible-at-scale-8`.
  - *Certificate.* The (D) prefix of the lifted domination core stops at the D-stuck set `a8_8` (40,442 points).
    From there, 5,152 (K) moves, all on norm-8 points, release (D) cascades that reach `{e_8}`. The certificates for
    `k ≤ 7` need at most 672 K moves each.
  - *Verification.* Two verifiers that share no code with the search replay every line from all of `Lmax_k`, with
    explicit `d_1` distances (`experiments/zn-rips-link-collapse-2026-09-18/`).
  - *Next.* `(8, 9)`. The D-stuck set after the prefix has 113,321 points, 2.8 times as many as `a8_8`. A (K)
    search on it fits in about 1.6 GB of bit rows. At `(8, 8)` the search needed about 4,000 s of wall time for
    5,152 K moves, and at `(8, 9)` both the rows and the links are larger. So `(8, 9)` needs many budgeted stages,
    or a partition-level (orbit) form of the (K) move.
  - *(8, 9), D-only is ruled out.* The D-stuck set `a8_9` (113,321 points) is itself self-blocking. The greatest
    fixed-point pass `F(a8_9) = a8_9` removes nothing, and `kchk` confirms the set piece by piece
    (`z8-rips-lifted-domination-certificates-fail-at-scale-9`). So `(8, 9)` needs (K) moves, just as `(8, 8)` did.
  - *(8, 9), partial (K) certificate.* It is in `experiments/zn-rips-link-collapse-scale-9-2026-09-18/partial/`.
    - Twelve budgeted `kzf` stages make 11,148 (K) moves and 6,602 cascaded (D) moves, taking `a8_9` down to
      95,571 points.
    - All 12 stages are replayed by `kzv5`, and the end sets match.
    - This is *not* a proof of `(8, 9)`.
  - *Next.* Resume `kzf` from `partial/end-stage-12-8-9.txt.gz` and replay each new stage with `kzv5`.
    - At `(8, 8)`, the (K) moves were exactly the norm-8 points with `x_8 = 0`. Extrapolating, about 10k more (K)
      moves are needed, roughly 5 CPU-hours.
    - `(8, 10)` does not fit in 2 GB with bit adjacency (186,502 D-stuck points, about 4.3 GB). It needs sparse links.
- **w7-103, (8, 9) closed.** `(8, 9)` is closed: `z8-rips-contractible-at-scale-9`.
  - *Certificate.* The w6-103 partial certificate is continued by a 13th `kzf`-type stage (754 (K) moves) and then
    by (K) moves restricted to the 11,170 norm-9 points with `x_8 = 0` that remain. These were searched as three
    parallel segments, which were then joined. In all, the `k = 8` certificate has 299,207 moves, 22,634 of them (K).
    Every (K) move deletes a norm-9 point with `x_8 = 0`.
  - *Pattern.* After stage 13, deleting those 11,170 points outright leaves a set that collapses by (D) alone. So
    at both `(8, 8)` and `(8, 9)`, (K) is needed only on the top shell `|x| = r` with `x_n = 0`.
  - *Verification.* `vcert2` replays the (D) prefix from `Lmax_8` down to `a8_9`. `kzv5` replays everything after
    that, in independent stretches whose end sets are compared with the predicted ones. `kzv5` and `kzv3` replay
    `k = 2..7`.
  - *Next.* `(8, 10)`. `kzs` (implicit SAD adjacency, `O(M + s²/8)` memory) runs at about 200 MB and about 1.6
    CPU-s per (K) move on a 205,606-point set. There are about 19k norm-10 points with `x_8 = 0`, so the (K) phase is
    about 8 CPU-hours. It should be run as parallel `KZ_KLIST` segments from a true D-stall set of `ilv4`.
- **w8-103, (8, 10) reduced to a top-shell deletion problem.** See `z8-rips-scale-10-reduces-to-top-shell-link-collapses`.
  - *Domination parts.* Two verified (D) certificates handle everything outside one explicit set:
    - 442,086 moves take `Lmax_8` (628,232 points) to a 186,146-point set `O`;
    - 167,329 moves take `O ∖ T` to `{e_8}`.
  - *The set `T`.* `T` is the 18,816 norm-10 points of `O` with `x_8 = 0`. These are exactly the points whose
    magnitude profile is `(3,2,2,1,1,1)` or a 7-part partition of 10.
  - *What is left.* Delete `T` from `O` with (K) moves. The `k ≤ 7` certificates at `r = 10` are already on main.
  - *(K) progress.* The (K) search (`kzs2`) and the verifier (`kzv6`) avoid the `M × M` matrix, which would need
    about 4 GB here. On the shared host the search takes about 2–6 wall-s per (K) line in each chain.
    - `T` is split into four blocks of 4,704 points.
    - Each block is searched from `O` minus the earlier blocks. The blocks join exactly when each one deletes just
      its own points by (K).
    - When staged, the chains had deleted 15,242 of the 18,816 points. The fourth chain had finished its block and
      ended at exactly `O ∖ T`. 3,574 points were left, all in the first three blocks.
    - 2,572 of the (K) lines are replayed by `kzv6`. The rest are search tier.
  - *Next.* Continue chains A, B and C from their last stage sets in
    `experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/`, verify each stage with `vpiece6.sh`, and
    concatenate.

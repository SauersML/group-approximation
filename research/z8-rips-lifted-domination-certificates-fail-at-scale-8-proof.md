---
rg: 2
id: z8-rips-lifted-domination-certificates-fail-at-scale-8-proof
kind: route
title: A self-blocking subset of Lmax_8 at scale 8, found as a greatest fixed point and checked by pairwise distances
target: z8-rips-lifted-domination-certificates-fail-at-scale-8
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, experiments/zn-rips-lifted-domination-core-2026-09-18/README.md, experiments/zn-rips-lifted-domination-core-2026-09-18/kchk.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/gfp.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/results.txt, experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K8_8.txt.gz, experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K6_6.txt.gz, experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K7_7.txt.gz, experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K7_8.txt.gz, experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K7_9.txt.gz]
---

Notation is that of `research/z7-rips-contractible-at-scale-10-proof.md`, §3:
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }`;
- `E = e_k`;
- `hull(S)` is the smallest integer box containing `S`;
- `N[v] = { z : d_1(z, v) ≤ r }`.

## 1. Self-blocking sets

Call `K ⊆ Lmax_k` **self-blocking** if `e_k ∈ K` and for every `x ∈ K ∖ {e_k}` and every
`w ∈ hull(0, x, E) ∩ Lmax_k` with `w ≠ x` there is `z ∈ K` with `d(z, x) ≤ r < d(z, w)`.

**Lemma B.** If `K` is self-blocking and `K ≠ {e_k}`, no sequence of (D) moves starting at `Lmax_k` ends at `{e_k}`.

*Proof.* Moves only delete points. So a sequence ending at `{e_k}` never deletes `e_k`, and it deletes every point
of `K ∖ {e_k}`, which is nonempty. Let `x` be the first point of `K ∖ {e_k}` it deletes, by the move `x | w`, and let
`C` be the current set just before that move. Then `K ⊆ C`.

The move requires `w ∈ C ⊆ Lmax_k`, `w ∈ hull(0, x, E)` and `w ≠ x`. So self-blocking gives `z ∈ K ⊆ C` with
`d(z, x) ≤ r < d(z, w)`, that is, `z ∈ (N[x] ∩ C) ∖ N[w]`. This contradicts `N[x] ∩ C ⊆ N[w]`. ∎

Two remarks on the proof:
- It uses nothing about the order of the moves, the dominators chosen, or any symmetry. So it rules out every
  (D)-only certificate, including the expansions of the orbit certificates of
  `z7-rips-contractible-at-scales-11-13-15-17-proof`.
- Candidates `w` with `d(x, w) > r` are blocked by `z = x`, so only `d(x, w) ≤ r` needs work.

**Greatest self-blocking set.** Let `F(K)` be the set of `x ∈ K` such that no `w ∈ hull(0, x, E) ∩ Lmax_k ∖ {x}` has
`N[x] ∩ K ⊆ N[w]`, together with `e_k`. Note that `e_k` has no candidates, since `hull(0, e_k, E) ∖ {e_k} = {0}`.
- `F` is monotone: blocking in a smaller `K` implies blocking in a larger one.
- Its fixed points are exactly the self-blocking sets.
- Iterating from `Lmax_k`, deleting points in place, reaches the greatest one, `K*(k, r)`.
- If a (D)-only certificate exists, then `K*(k, r) = {e_k}`.

The converse is not claimed: the relaxation lets `w` range over all of `Lmax_k`.

## 2. The set at (8, 8)

`experiments/zn-rips-lifted-domination-core-2026-09-18/cores/K8_8.txt.gz` lists 16,114 points of `Lmax_8` at
`r = 8`. It contains `e_8`.

The checker `kchk.cpp` (`./kchk 8 8 K8_8.txt`) proves it self-blocking by pairwise distances only. It does no
search over the ball and shares no code with the search programs. It checks:
- every point lies in `Lmax_8`, there are no duplicates, `e_8 ∈ K`, and `|K| > 1`;
- for each `x ∈ K ∖ {e_8}`, it lists `N[x] ∩ K` by scanning `K`;
- it enumerates every `w ∈ hull(0, x, E)` with `|w| ≤ 8`, `w ≻ 0` and `w ≠ x`;
- for each such `w`, it finds some `z` in that list with `d(z, w) > 8`.

Output: `OBSTRUCTION VERIFIED: k=8 r=8 |K|=16114`. All 1,567,975 pairs `(x, w)` are blocked, using 712,820,417
distance tests on the sorted file as landed, in 7 s. The count of distance tests depends on the file order; the count
of pairs does not. By Lemma B, the claim follows. ∎

## 3. How the set was found, and further data (not used in §2)

`K8_8` is the set left when a point-level greedy with (D) and (K) moves stalls at `(8, 8)` (see the README). `gfp.cpp`
takes it as a start set. It iterates `F` with `w` over all of `Lmax_8` and finds `F(K8_8) = K8_8` in one pass,
with 0 removals. The full iteration from `Lmax_8` exceeds the 20-minute budget. After one pass (850 s) it is down to
40,496 points.

Full greatest fixed points `K*(k, r)`, computed by `gfp.cpp` from `Lmax_k` and each re-verified by `kchk`:

| (k, r) | `|Lmax_k|` | `|K*|` |
|---|---|---|
| (4, 4) | 160 | 1 |
| (5, 5) | 841 | 1 |
| (5, 6) | 1,826 | 1 |
| (5, 9) | 11,181 | 1 |
| (6, 6) | 4,494 | 883 |
| (6, 7) | 9,912 | 1 |
| (6, 8) | 20,040 | 1 |
| (6, 9) | 37,758 | 1 |
| (7, 7) | 24,319 | 6,720 |
| (7, 8) | 54,272 | 10,392 |
| (7, 9) | 112,071 | 23,830 |

Each nontrivial set in this table is in `cores/` and passes `kchk`. A value of 1 means only that this obstruction
is absent; it does not give a certificate. The runs `(8, 8)` and `(8, 9)` from `Lmax_8` did not finish within the
budget. So whether `K*(8, r) = {e_8}` for some `r ≥ 9` is open.

These fit the known certificates:
- For its unlifted framework, `z7-rips-contractible-at-scales-7-and-8` reports that D-moves alone leave 6,721 and
  10,393 survivors at `(7, 7)` and `(7, 8)`, and it closes those scales with link collapses.
- `(7, 11)`, `(7, 13)`, `(7, 15)` and `(7, 17)` have (D)-only certificates, so `K* = {e_7}` there.

The points of `K8_8` have all coordinates in `{−2, …, 2}`, and 9,678 of them have exactly one coordinate of absolute
value 2. With layers indexed `0, …, 7`, the set meets every norm from 1 to 8 and every layer, and 9,111 of its points
lie in the top layer 7. It is far from invariant under the signed permutations of the lower coordinates.

The small points it contains are pinned by sphere points. For example, `x = (1, 0, …, 0)` is blocked for `w = E` by
any `z ∈ K` of norm 8 with `z_0 ≥ 1` and last coordinate `0`, since then `d(z, x) = 7` and `d(z, E) = 9`.

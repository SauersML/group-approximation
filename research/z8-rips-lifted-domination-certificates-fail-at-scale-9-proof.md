---
rg: 2
id: z8-rips-lifted-domination-certificates-fail-at-scale-9-proof
kind: route
title: A 113,321-point self-blocking subset of Lmax_8 at scale 9, checked by pairwise distances
target: z8-rips-lifted-domination-certificates-fail-at-scale-9
requires: []
artifacts: [research/z8-rips-lifted-domination-certificates-fail-at-scale-8-proof.md, experiments/zn-rips-lifted-domination-core-2026-09-18/kchk.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/README.md, experiments/zn-rips-link-collapse-scale-9-2026-09-18/gfpr.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/kchkr.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/results.txt, experiments/zn-rips-link-collapse-scale-9-2026-09-18/cores/K8_9.txt.gz]
---

Notation and the definition of a self-blocking set are those of
`research/z8-rips-lifted-domination-certificates-fail-at-scale-8-proof.md`, §1. Here `k = 8`, `r = 9`,
`E = e_8`, and `N[v]` is the closed `d_1`-ball of radius 9.

## 1. The lemma used

`K ⊆ Lmax_k` is **self-blocking** if `e_k ∈ K` and, for every `x ∈ K ∖ {e_k}` and every
`w ∈ hull(0, x, E) ∩ Lmax_k` with `w ≠ x`, there is `z ∈ K` with `d(z, x) ≤ r < d(z, w)`.

**Lemma B** (as in loc. cit., §1). If `K` is self-blocking and `K ≠ {e_k}`, no sequence of (D) moves that starts at
`Lmax_k` ends at `{e_k}`.

*Proof.*
1. Moves only delete points. So a sequence ending at `{e_k}` never deletes `e_k`.
2. It does delete every point of `K ∖ {e_k}`, and that set is nonempty. Let `x` be the first point of `K ∖ {e_k}`
   it deletes, by the move `x | w`, and let `C` be the current set just before that move. Then `K ⊆ C`.
3. The move needs `w ∈ C ⊆ Lmax_k`, `w ∈ hull(0, x, E)` and `w ≠ x`. So self-blocking gives some `z ∈ K ⊆ C` with
   `d(z, x) ≤ r < d(z, w)`. That is, `z ∈ (N[x] ∩ C) ∖ N[w]`.
4. This contradicts the move condition `N[x] ∩ C ⊆ N[w]`. ∎

The proof does not need `K` to be the greatest self-blocking set, only a self-blocking one.

## 2. The set

`experiments/zn-rips-link-collapse-scale-9-2026-09-18/cores/K8_9.txt.gz` lists 113,321 points of `Lmax_8` at
`r = 9`, sorted, one per line. It contains `e_8`.

The checker is `experiments/zn-rips-lifted-domination-core-2026-09-18/kchk.cpp`, the one already on main. It proves
the set self-blocking using pairwise distances only:
- every point lies in `Lmax_8` at `r = 9`, there are no duplicates, `e_8 ∈ K`, and `|K| > 1`;
- for each `x ∈ K ∖ {e_8}`, it lists `N[x] ∩ K` by scanning `K`;
- it enumerates every `w ∈ hull(0, x, E)` with `|w|_1 ≤ 9`, `w ≻ 0` and `w ≠ x`;
- for each such `w`, it finds some `z` in that list with `d(z, w) > 9`.

At `|K| = 113,321` one run exceeds the 1200 s wall limit per run. So the check is split by index:
- `experiments/zn-rips-link-collapse-scale-9-2026-09-18/kchkr.cpp` is `kchk.cpp` with two changes:
  - it takes an optional index range `[lo, hi)`;
  - it checks the per-`x` condition only for the entries of the file in that range.
- Every run still does all of the global checks (membership, duplicates, `e_8`, `|K| > 1`).
- The piece counts on the (7,7) core add up to the full `kchk` counts. The test is recorded in `results.txt`.

`./kchkr 8 9 K8_9.txt lo lo+10000` for `lo = 0, 10000, …, 110000` covers every index. Each piece prints
`PIECE VERIFIED`. The twelve output lines, with their pair counts and run times, are in `results.txt`.

Hence `K` is self-blocking. By Lemma B the claim follows. ∎

## 3. How the set was found (not used in §2)

- `ilv4.cpp` (`./ilv4 8 9 c8_9.txt - a8_9.txt 1100 400`) peels `Lmax_8` (299,208 points at `r = 9`) by (D) moves and
  stalls at a 113,321-point set `a8_9`. `vcert2.cpp` replays those 185,887 moves from all of `Lmax_8` and reports
  `all moves valid` and `left=113321`.
- `gfpr.cpp` is `gfp.cpp` of the same directory with a wall-clock budget and a resume position, so a pass can be
  split across runs. Started from `a8_9`, it iterates the map `F` of loc. cit. §1, with `w` ranging over all of
  `Lmax_8`. It finds `F(a8_9) = a8_9`, with no removals, and prints
  `RESULT k=8 r=9 |K|=113321 K != {e_k}: NO (D)-only certificate exists`.
- `K8_9` is `a8_9`, sorted. The check in §2 is independent of this search.

Because `F` is monotone, the greatest self-blocking set `K*(8, 9)` contains `K8_9`, so it has at least 113,321 points.
Whether it is larger is not needed and was not computed.

For comparison, at `(8, 8)` the stall set of the same greedy has 40,442 points, and the self-blocking set on main has
16,114 points. At `(8, 9)` the stall set is self-blocking as it stands.

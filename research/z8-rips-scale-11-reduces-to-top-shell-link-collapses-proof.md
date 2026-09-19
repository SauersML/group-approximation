---
rg: 2
id: z8-rips-scale-11-reduces-to-top-shell-link-collapses-proof
kind: route
title: Two domination certificates at (8, 11), around an explicit top-shell set, replayed by vcert2
target: z8-rips-scale-11-reduces-to-top-shell-link-collapses
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, research/z7-rips-contractible-at-scales-11-13-15-17-proof.md, research/z8-rips-contractible-at-scale-8-proof.md, experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp, experiments/zn-rips-link-collapse-scale-11-2026-09-19/README.md, experiments/zn-rips-link-collapse-scale-11-2026-09-19/results.txt, experiments/zn-rips-link-collapse-scale-11-2026-09-19/ilv5.cpp, experiments/zn-rips-link-collapse-scale-11-2026-09-19/topshell11.py, experiments/zn-rips-link-collapse-scale-11-2026-09-19/kzc1.cpp, experiments/zn-rips-link-collapse-scale-11-2026-09-19/kzc1-stages.sh, experiments/zn-rips-link-collapse-scale-11-2026-09-19/vchain.sh, experiments/zn-rips-link-collapse-scale-11-2026-09-19/vtail.sh, experiments/zn-rips-link-collapse-scale-11-2026-09-19/sets/O-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/sets/T-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/certs/d-prefix-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/certs/d-tail-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/certs/k-sample-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/certs/k-formula-single-8-11.txt.gz, experiments/zn-rips-link-collapse-scale-11-2026-09-19/certs/k-formula-chain-8-11.txt.gz]
---

Notation is that of the target and of `research/z7-rips-contractible-at-scale-10-proof.md` (§3). Here `k = 8`,
`r = 11` and `E = e_8`. All files below are in `experiments/zn-rips-link-collapse-scale-11-2026-09-19/` unless a path
says otherwise. Every run is recorded in `results.txt`, with the sha256 of every input.

## 1. Part (1): `Lmax_8 → O`

`certs/d-prefix-8-11.txt.gz` has 843,210 lines: 330,520 `A` lines and 512,690 `D` lines. Both are (D) moves in the
format of `vcert2.cpp`. The search was `ilv4` of `experiments/zn-rips-lifted-domination-core-2026-09-18/` for the
first three stages and `ilv5.cpp` for the last three (README).

**Check.** `experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp` is on main and shares no code with the
search. `vchain.sh` replays the file from all of `Lmax_8` in 34 chunks of at most 25,000 lines, chained with
`-o`/`-i`.
- The first chunk starts from `Lmax_8` (1,242,912 points).
- Every chunk prints `all moves valid`.
- The last chunk ends with `left=399702`.
- The final state file, sorted, equals `sets/O-8-11.txt.gz` exactly (`PREFIX VERIFIED`).

`vcert2` checks the (D) condition as the absence of a present `z` with `d(z, x) ≤ r < d(z, w)`. It finds such a `z`
by a DFS over a rank bitmap of the `l^1` ball, and it checks the hull and presence conditions coordinatewise.

## 2. Part (2): the top shell of `O`

`topshell11.py` enumerates `T` from its definition, going through all `x` with `|x|_1 = 11`, `x_8 = 0` and `x ≻ 0`.
It then checks three things:
- `T ⊆ O`;
- `{ x ∈ O : |x|_1 = 11, x_8 = 0 }`, minus its points of profile `(5,1^6)`, equals `T`;
- `sets/T-8-11.txt.gz` lists exactly `T`.

It prints `|T| = 53312`, 48 points of profile `(5,1^6)`, and `TOPSHELL VERIFIED`. Its profile table:

| last nonzero index | profile | support | points |
|---|---|---|---|
| 6 | (4,2,2,1^3), (3,3,2,1^3), (3,2,2,2,1,1) | 6 | 1,920 each |
| 7 | (4,2,2,1^3), (3,3,2,1^3), (3,2,2,2,1,1) | 6 | 11,520 each |
| 7 | (4,2,1^5) | 7 | 2,688 |
| 7 | (3,3,1^5) | 7 | 1,344 |
| 7 | (3,2,2,1^4) | 7 | 6,720 |
| 7 | (2^4,1^3) | 7 | 2,240 |

Each row is a complete class. For example, for `(3,2,2,2,1,1)` with last index 7: 6 choices of the zero among the
first 6 coordinates, 60 arrangements, 2^5 signs on the first 6 coordinates, and `x_7 > 0`, i.e. `6 · 60 · 32 = 11,520`.

## 3. Part (3): `O ∖ T → {e_8}`

`certs/d-tail-8-11.txt.gz` has 346,389 `D` lines. Its start set is `O ∖ T`, which has 346,390 points. It is obtained
by removing the lines of `sets/T-8-11.txt.gz` from `sets/O-8-11.txt.gz`. It came from `KZ_DONLY=1` runs of `kzs2` of
`experiments/zn-rips-link-collapse-scale-10-2026-09-18/` (two budgeted pieces).

**Check.** `vtail.sh` replays it with `vcert2`, from `-i` the start set, in 14 chunks. Every chunk prints
`all moves valid`, and the last one ends at `{e_8}` (exit code 0, `TAIL VERIFIED`).

## 4. The consequence

All moves only delete points, and the (D) and (K) conditions refer only to the current set. So a concatenation of
certificates is a certificate when each piece starts where the previous one ends. The pieces are §1 (from `Lmax_8`
to `O`), any sequence from `O` to `O ∖ T`, and §3 (from `O ∖ T` to `{e_8}`). Together they are a lifted certificate
at `(8, 11)` ending at `{e_8}`.

The certificates for `k = 2, …, 7` at `r = 11` are `experiments/zn-rips-layered-orbits-2026-09-18/certs/c<k>-11.txt.gz`
of `z7-rips-contractible-at-scales-11-13-15-17-proof`. Each orbit line there expands to (D) moves on `Lmax_k`, and the
theorem of `z7-rips-contractible-at-scale-10-proof` only needs, for each `k ≤ n`, a certificate on `Lmax_k` at scale
`r`. `Lmax_k` does not depend on `n`, so the theorem applies at `n = 8`. ∎

## 5. Not part of the claim: the (K) phase on `T`

Nothing in §1–§4 uses (K) moves. This section records what is known about the missing piece `O → O ∖ T`.
- **Sample.** `certs/k-sample-8-11.txt.gz` came from `KZ_KFIRST` `kzs2` on 21 points of `T` against `C = O`. All
  21 (K) moves succeed. The witnesses found are `w = e_7 + e_8` for 13 of the 18 points with `x_7 ≠ 0`, and `u'
  + e_8` for the other 8, where `u'` is `u` with its largest coordinates moved towards 0 (README).
- **Formula witness.** For `u ∈ T` with last nonzero index `j`, let `w(u) = e_j + e_8`. `kzc1` (§6) accepts `K u |
  w(u)` from `C = O`, alone, for 24 of 24 random points of `T` (12 with `j = 7`, 12 with `j = 6`;
  `certs/k-formula-single-8-11.txt.gz`). It also accepts a sequential chain of 40 such lines, the 40 points of `T`
  nearest to `u0 = (2,-1,1,1,-3,1,2,0)`, ending at 399,662 points (`certs/k-formula-chain-8-11.txt.gz`). These 64
  lines are all the formula lines tried. None failed.
- **Cost.** One (K) check against `C ≈ O` takes 4–13 core-seconds in `kzc1`. So a certificate for all of `T` is
  about `53,312 × 8 s ≈ 120` core-hours of checking, and it has to be split into block chains. The join rule of
  `z8-rips-contractible-at-scale-10` applies: each block is replayed from the end set of the previous one.

## 6. `kzc1`, and the (K) lines of `(8, 10)`

`kzc1.cpp` is a checker for `K` and `D` lines, written from the definitions. It shares no code with `kzs2`, `kzs3`,
`kzv6`, `kzv7` or `vcert2`.
- It has its own tokenizer, and it keeps points in a rank table rather than a hash.
- Distances are `l^1` sums of byte-column differences, with no SIMD sum of absolute differences.
- A `D` line `x | w` is checked by an explicit scan of `C` for a `z` with `d(z, x) ≤ r < d(z, w)`, together with
  presence and the hull condition.
- A `K` line `u | w` is checked by collapsing the link `N(u) ∩ C`, as bit rows, until it is a cone on `w`. Hull
  filters use prefix unions of boxes. Every removal is re-checked with explicit distances. A final explicit test
  requires every point left in the link to be within `r` of `w`.

`kzc1 k r Ofile cert first last end` applies lines before `first` only as deletions, checks lines `first..last`,
and writes the end set.

The (8, 10) certificate of `z8-rips-contractible-at-scale-10` has 987 (K) lines from `kzs3`. Before this, only
`kzv7` had replayed them, and `kzv7` shares parsing and distance code with `kzs3`. `kzc1-stages.sh` replays the six
`kzs3` stages of that certificate's middle piece in 12-line chunks: `E2` (lines 8366–8518), `E3` (8519–8663), `E4`
(8664–8848), `F2` (8905–9025), `F3` (9026–9336) and `F4` (9337–9408). That is 153 + 145 + 185 + 121 + 311 + 72 = 987
lines. For each stage it compares the sorted end set with the start set recorded in that node's
`chains/stage-index.txt`.

**Result.** All 987 lines ACCEPT, and all six end sets MATCH: 177,628, 177,483, 177,298, 177,121, 176,810 and
176,738 points (`results.txt`). So the (K) lines of `(8, 10)` now have a replay that is independent of the search
code.

---
rg: 2
id: z8-rips-scale-10-reduces-to-top-shell-link-collapses-proof
kind: route
title: Two domination certificates at (8, 10), around an explicit top-shell set, replayed by two independent verifiers
target: z8-rips-scale-10-reduces-to-top-shell-link-collapses
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, research/z8-rips-contractible-at-scale-8-proof.md, experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/README.md, experiments/zn-rips-link-collapse-scale-10-2026-09-18/results.txt, experiments/zn-rips-link-collapse-scale-10-2026-09-18/topshell.py, experiments/zn-rips-link-collapse-scale-10-2026-09-18/kzs2.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/kzv6.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/vpiece6.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/O-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/T-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/certs/d-prefix-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/certs/d-tail-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/stall-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/certs/d-stall-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segchain.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/vloop.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/stageseg.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/TA.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/TB.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/TC.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/TD.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/k-segA-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/k-segB-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/k-segC-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/segments/k-segD-8-10.txt.gz]
---

Notation is that of the target and of `research/z7-rips-contractible-at-scale-10-proof.md` (§3). Here `k = 8`,
`r = 10` and `E = e_8`. All files below are in `experiments/zn-rips-link-collapse-scale-10-2026-09-18/` unless a path
says otherwise. Every run is recorded in `results.txt`, with the sha256 of every input.

## 1. Part (1): `Lmax_8 → O`

`certs/d-prefix-8-10.txt.gz` has 442,086 lines: 227,648 `A` lines and 214,438 `D` lines. Both are (D) moves in the
format of `vcert2.cpp`.

**Check.** `experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp` is on main and shares no code with the
search. It replays the file from all of `Lmax_8` in 18 chunks of 25,000 lines, chained with `-o`/`-i`.
- The first chunk prints `start present=628232 (= |Lmax|)`.
- Every chunk prints `all moves valid`.
- The last chunk ends with `left=186146`.
- The final state file, sorted, equals `sets/O-8-10.txt.gz` exactly.

`vcert2` checks the (D) condition as the absence of a present `z` with `d(z, x) ≤ r < d(z, w)`. It finds such a `z`
by a DFS over a rank bitmap of the `l^1` ball, and it checks the hull and presence conditions coordinatewise.

## 2. Part (2): the top shell of `O`

`topshell.py` enumerates `T` from its definition, going through all `x` with `|x|_1 = 10`, `x_8 = 0` and `x ≻ 0`.
It then checks three things:
- `T ⊆ O`;
- `{ x ∈ O : |x|_1 = 10, x_8 = 0 } = T`;
- `sets/T-8-10.txt.gz` lists exactly `T`.

It prints `|T| = 18816` and `TOPSHELL VERIFIED`. The profile table it prints is as follows.

| last nonzero index | profile | support | points |
|---|---|---|---|
| 6 | (3,2,2,1,1,1) | 6 | 1,920 |
| 7 | (3,2,2,1,1,1) | 6 | 11,520 |
| 7 | (4,1^6) | 7 | 448 |
| 7 | (3,2,1^5) | 7 | 2,688 |
| 7 | (2^3,1^4) | 7 | 2,240 |

Each row is a complete class: for example, row 2 is 6 zero positions × 60 arrangements × 2^5 signs.

## 3. Part (3): `O ∖ T → {e_8}`

`certs/d-tail-8-10.txt.gz` has 167,329 `D` lines. Its start set is `O ∖ T`, which has 167,330 points. It is obtained
by removing the lines of `sets/T-8-10.txt.gz` from `sets/O-8-10.txt.gz`. Two verifiers replay it:
- **`vcert2`**, from `-i` the start set, in 7 chunks. Every chunk prints `all moves valid`, and the last one ends
  with `left=1`, i.e. at `{e_8}`.
- **`kzv6.cpp`** (§5). It prints `END={e_k} ACCEPT`.

## 4. The consequence

All moves only delete points, and the (D) and (K) conditions refer only to the current set. So a concatenation of
certificates is a certificate when each piece starts where the previous one ends. The pieces are §1 (from `Lmax_8`
to `O`), any sequence from `O` to `O ∖ T`, and §3 (from `O ∖ T` to `{e_8}`). Together they are a lifted certificate
at `(8, 10)` ending at `{e_8}`.

The certificates for `k = 2, …, 7` at `r = 10` are `experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k<k>.txt.gz`
of `z7-rips-contractible-at-scale-10-proof`. That route's theorem only needs, for each `k ≤ n`, a certificate on
`Lmax_k` at scale `r`, and `Lmax_k` does not depend on `n`. So the theorem applies at `n = 8`. ∎

## 5. The tools for the (K) phase

- **`kzv6.cpp`** is self-contained. It checks the compact `D`/`K` line format of `z8-rips-contractible-at-scale-8-proof`
  (§2), with the same maximal protected collapse. It is the `kzv5` verifier of the `(8, 9)` work of w6-103 and
  w7-103, but without its global `M × M` bit matrix. At `(8, 10)` that matrix would need about 4 GB at `|O|`.
  - Neighbourhoods are recomputed for each line from packed coordinates, one byte per coordinate plus 64.
    `vpsadbw` sums absolute byte differences, which is exactly the `l^1` distance.
  - A deleted point is packed as all-ones, so it is never within `r` of anything.
  - The (K) check is the maximal protected collapse, unchanged from kzv5.
  - Tests are in `results.txt`:
    - on a `k = 5`, `r = 9` certificate and on 30 (K) lines at `(8, 9)` it gives the same end sets and collapse-step
      counts as `kzv5`;
    - a (K) line relabelled as (D) is rejected.
- **`kzs2.cpp`** is the search. It is the `kzs` search of w7-103 with AVX-512 neighbourhoods and link rows. It adds
  `KZ_KLIST=file`, which tries (K) only at the listed points, and `KZ_DONLY=1`, which stops after the (D) sweeps.
  The certificate in §3 came from `KZ_DONLY=1 ./kzs2 8 10 O∖T …`.

## 6. Partial progress on the middle piece (not used by the claim)

The claim does not depend on this section. It records how far the deletion of `T` has gone.
- `segments/` holds four (K) chains, one for each block of a partition of `T` into four blocks of 4,704 points.
- Each chain uses only (K) lines at points of its own block. The chain for the first block starts at `O`, and each
  later chain starts at `O` minus the earlier blocks. So once every chain has finished its block, the chains join
  exactly (README, "Join rule").
- Status when staged: the chains delete 15,242 of the 18,816 points of `T`, and 3,574 are left in the first three
  blocks. The fourth chain has finished its block and ends at exactly `O ∖ T`, which is the start set of §3.
- Tiers: 2,572 of the (K) lines, the first one or two stages of each chain, are replayed by `kzv6` from their start
  sets, with exactly the end sets of the search. The rest are search tier (`kzs2`). The table is in the README.

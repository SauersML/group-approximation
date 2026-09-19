---
rg: 2
id: z8-rips-contractible-at-scale-10-proof
kind: route
title: The (8, 10) lifted certificate, completed by six (K) chains that delete the top shell T
target: z8-rips-contractible-at-scale-10
requires: [z8-rips-scale-10-reduces-to-top-shell-link-collapses]
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, research/z8-rips-scale-10-reduces-to-top-shell-link-collapses-proof.md, experiments/zn-rips-link-collapse-scale-10-2026-09-18/README.md, experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/O-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/T-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/kzv6.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/kzs2.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/README.md, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/results.txt, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/kzs3.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/kzv7.cpp, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/vpiece7.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/mkord.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/segchain3.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/finish.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/v7queue.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/assemble.sh, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/chains/blocks-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/chains/k-middle-8-10.txt.gz, experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/chains/stage-index.txt]
---

Notation is that of `z8-rips-scale-10-reduces-to-top-shell-link-collapses` and its route: `k = 8`, `r = 10`, `E = e_8`,
`O` (186,146 points) is the end set of the d-prefix, `T ⊆ O` is the top shell (18,816 points), and the d-tail takes
`O ∖ T` to `{e_8}`. Files are in `experiments/zn-rips-link-collapse-scale-10-2026-09-18/complete/` unless a path
says otherwise.

The target's route proves that any sequence of valid moves from `O` to `O ∖ T` completes a lifted certificate at
`(8, 10)` ending at `{e_8}`, and hence the claim (its §4). This route supplies that sequence: 18,816 (K) lines, one at
each point of `T`, in `chains/k-middle-8-10.txt.gz`.

## 1. The middle piece

`T` is split into the four blocks `TA, TB, TC, TD` of 4,704 points each of the target's route (`segments/T?.txt.gz`
there). The chain for `TB` had 1,120 points of `TB` left after 13 stages, so these were split again into `TE` (the
first 560 in the order of `TB`) and `TF` (the other 560), run as two chains. `chains/blocks-8-10.txt.gz` lists every point of `T` with its block
letter, and `TA ∪ TB ∪ TC ∪ TD = T` with `TB = TB' ∪ TE ∪ TF` disjointly, where `TB'` is the part of `TB` that its
chain deleted.

The middle piece is six chains, in this order:

| chain | start set | end set | (K) lines | stages |
|---|---|---|---|---|
| A | `O` | `O ∖ TA` | 4,704 | 13 |
| B | `O ∖ TA` | `O ∖ (TA ∪ TB')` | 3,584 | 13 |
| E | `O ∖ (TA ∪ TB')` | `O ∖ (TA ∪ TB' ∪ TE)` | 560 | 4 |
| F | `O ∖ (TA ∪ TB' ∪ TE)` | `O ∖ (TA ∪ TB)` | 560 | 4 |
| C | `O ∖ (TA ∪ TB)` | `O ∖ (TA ∪ TB ∪ TC)` | 4,704 | 13 |
| D | `O ∖ (TA ∪ TB ∪ TC)` | `O ∖ T` | 4,704 | 10 |

Each chain uses (K) lines only at points of its own block, so it deletes exactly its block. Each end set is,
as a set, exactly the start set of the next row, and the last end set is the start set of the d-tail. Every chain
is cut into stages (one search run each); `chains/stage-index.txt` gives, for every stage, its line range in
`k-middle-8-10.txt.gz`, the size and sha256 of its sorted start set, and the tier of its lines (§3).

## 2. The (K) move and why a chain is valid

A line `K u | w` is valid at the current set `C` when `u, w ∈ C`, `w ≠ u`, `d(u, w) ≤ r`, `w` lies in the box
`hull(0, u, E)`, and the maximal protected collapse of the link `S = N(u) ∩ C ∖ {u}` ends inside `N[w]`. The collapse
removes `b ≠ w` when some `v ∈ cur`, `v ≠ b`, with `d(b, v) ≤ r` and `v ∈ hull(0, u, b, E)`, has
`N[b] ∩ cur ⊆ N[v]`. This is the move of `z8-rips-contractible-at-scale-8-proof` (§2), unchanged.

The chains were found by two searches.
- **`kzs2.cpp`** (of the target's route, with `KZ_KLIST`) found chains A, B, C, D and the first stage of E and F.
- **`kzs3.cpp`** found the rest of E and F. It runs the same removal rule without the protection of `w` and stops
  as soon as some `w ∈ cur ∩ hull(0, u, E)` has `cur ⊆ N[w]`. It is only a proposal: the verifier then runs the
  maximal collapse protecting `w`.

A search run is not a proof. Every (K) line is accepted only when a verifier (§3) replays it from the exact start set
of its stage.

## 3. The replay and the tiers

**The verifiers.** `kzv6.cpp` (of the target's route) and `kzv7.cpp` check `D` and `K` lines with the same maximal
protected collapse. `kzv7` is `kzv6` with AVX-512 row builds and a hash table for lattice-neighbour lookups.
- On the same start file, `kzv6` and `kzv7` give the same verdicts, collapse-step counts and end sets
  (`results.txt`: 20 lines of stage E2, which `kzs3` found; a (K) line relabelled as (D) is rejected by both).
- Soundness needs only that the verifier's run is a sequence of valid removals ending inside `N[w]`, which is the
  move of `z8-rips-contractible-at-scale-8-proof` (§2). The run, and so its step count, depends on the order of the
  start file, because the collapse stops as soon as `cur ⊆ N[w]`.
- `mkord.sh` puts every stage's start set in the order of `O`. This fixes the order used here, so each replay can
  be reproduced exactly.

**Shared code.** `kzs3` reuses `kzv7`'s input parsing and packed `l^1` row code, but not its move check. So for the
lines found by `kzs3`, the verifier is independent in its acceptance test, not in its distance code. That distance
code (one byte per coordinate, `vpsadbw`) is the code of `kzv6`, which was checked against the pairwise `kzv5` in the
target's route. `kzs2` shares no code with either verifier.

**Replay.** `vpiece7.sh` replays a stage with `kzv7` in pieces of 1,000 wall seconds. It chains the pieces by
removing the deleted points from the start file, which keeps the scan order. It checks this set equal to the
verifier's own output at every pause, and at the end it checks the final set equal to the search's end set for the
stage. `v7queue.sh` runs the queue of stages.

**Tiers.** The middle piece has 57 stages. Every stage was replayed by `kzv7` from its exact start set, in the order
of `O`, and ended with every line accepted and the end set equal to the search's end set. Seven stages (A1, A2, B1,
B2, C1, C2, D1) were also replayed by `kzv6`, in the target's route. The last column of `chains/stage-index.txt`
records this for each stage, and `results.txt` has the verdict line of every piece.

## 4. The full certificate

The full `k = 8` certificate is the concatenation of
- `../certs/d-prefix-8-10.txt.gz` (442,086 (D) lines, `Lmax_8 → O`),
- `chains/k-middle-8-10.txt.gz` (18,816 (K) lines, `O → O ∖ T`), and
- `../certs/d-tail-8-10.txt.gz` (167,329 (D) lines, `O ∖ T → {e_8}`),

so 628,231 lines, one for each point of `Lmax_8` except `e_8`.

Replaying this file end to end is the same as replaying its stages in turn. Every move only deletes its point `u`,
and whether a line is valid depends only on the current set. So a line valid from the end set of the lines before
it stays valid wherever that set is reached. The replays reach, as exact sets, the end set of every stage:
- The d-prefix was checked by the chunked `vcert2` run of the target's route. It was checked again here by `kzv6`
  from `Lmax_8` in pieces, ending at `O`.
- Each of the 57 middle stages was checked from the end set of the one before (§3). The first starts at `O`, and
  the last ends at `O ∖ T`.
- The d-tail was checked by `kzv6` from `O ∖ T` in the target's route (`END={e_k} ACCEPT`).

So the replay of the concatenation ends at `END = {e_8}` with every line accepted. This gives a valid lifted
certificate at `(k, r) = (8, 10)`. By the target's route (§4), it proves the claim.

---
rg: 2
id: z8-rips-contractible-at-scale-9-proof
kind: route
title: Lifted domination and link-collapse certificates for k = 2..8 at scale 9, replayed by independent verifiers
target: z8-rips-contractible-at-scale-9
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, research/z8-rips-contractible-at-scale-8-proof.md, research/z8-rips-lifted-domination-certificates-fail-at-scale-9-proof.md, experiments/zn-rips-link-collapse-2026-09-18/genL.py, experiments/zn-rips-link-collapse-2026-09-18/kzv3.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/kzf.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/kzv5.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/cores/K8_9.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/partial/d-prefix-8-9.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/partial/k-stages-1-12-8-9.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/partial/end-stage-12-8-9.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/README.md, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/results.txt, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/kzh.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/kzs.cpp, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/vpiece.sh, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/segchain.sh, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k2.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k3.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k4.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k5.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k6.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/cert-9-k7.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/k8-stage-13.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/k8-seg-A.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/certs/k8-tail.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/sets/end-stage-13.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/sets/end-seg-A.txt.gz, experiments/zn-rips-link-collapse-scale-9-2026-09-18/complete/sets/T13.txt.gz]
---

Notation is as in `research/z7-rips-contractible-at-scale-10-proof.md` and `research/z8-rips-contractible-at-scale-8-proof.md`:
- `N[v]` is the closed neighbourhood at `d_1`-distance `≤ r`;
- `x ≻ 0` means the last nonzero coordinate of `x` is positive;
- `hull(S)` is the smallest integer box containing `S`;
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }` and `E = e_k`.

Here `n = 8` and `r = 9`. Every file named below without a directory is in
`experiments/zn-rips-link-collapse-scale-9-2026-09-18/`.

## 1. The reduction

This is the Theorem of `z8-rips-contractible-at-scale-8-proof` §1, from §1–§3 of
`z7-rips-contractible-at-scale-10-proof`. Those sections hold for every `(n, r)`.

**Theorem.** Suppose that for each `k = 2, …, n` there is a lifted certificate on `Lmax_k` at scale `r` that
ends at `{e_k}`. Then `VR(Z^n, d_1; r)` is contractible.

The moves are these.
- **(D) x | w.** Here `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and `N[x] ∩ C ⊆ N[w]`. Delete `x`.
- **(K) u | w.** This is written compactly. The verifier builds `S = N(u) ∩ C` and runs protected collapse
  steps `(b | v)`: `b, v` in the current `S`, `v ≠ b`, `v ∈ hull(0, u, b, E)` and `N[b] ∩ S ⊆ N[v]`. It then
  requires `w ∈ S ∩ hull(0, u, E)` and `S ⊆ N[w]`. Only then is `u` deleted.

The verifiers check every step they take. So an accepted compact (K) line, together with the verifier's run on
it, is a (K) move in the sense of the Theorem (`z8-rips-contractible-at-scale-8-proof` §2).

So it suffices to exhibit seven certificates at `r = 9`, one for each `k = 2, …, 8`.

## 2. k = 2, …, 7

The file `complete/certs/cert-9-k<k>.txt.gz` is a full certificate from `Lmax_k` to `{e_k}`. It was found by
`kzf.cpp`, in one budgeted stage for each `k`, starting from `L<k>.txt`. That file is written by
`python3 ../zn-rips-link-collapse-2026-09-18/genL.py k 9 L<k>.txt`.

`kzv5.cpp` replays each certificate from `L<k>.txt`. It checks that the start set is duplicate-free, lies in
`Lmax_k`, and has size `|Lmax_k| = (Σ_i 2^i C(k,i) C(9,i) − 1)/2`, so it is all of `Lmax_k`. Each replay ends at
`{e_k}` with ACCEPT. `kzv3.cpp` of `../zn-rips-link-collapse-2026-09-18/` accepts all six as well, again ending at `{e_k}`.

| k | `|Lmax_k|` | D-moves | K-moves | `kzv5` |
|---|---|---|---|---|
| 2 | 90 | 89 | 0 | ACCEPT, end `{e_2}` |
| 3 | 579 | 578 | 0 | ACCEPT, end `{e_3}` |
| 4 | 2,820 | 2,819 | 0 | ACCEPT, end `{e_4}` |
| 5 | 11,181 | 11,180 | 0 | ACCEPT, end `{e_5}` |
| 6 | 37,758 | 37,757 | 0 | ACCEPT, end `{e_6}` |
| 7 | 112,071 | 111,590 | 480 | ACCEPT, end `{e_7}` |

## 3. k = 8

`|Lmax_8| = 299,208`. The certificate is the concatenation of five files, in this order.

| # | file | D | K | start → end | replayed by |
|---|---|---|---|---|---|
| 1 | `partial/d-prefix-8-9.txt.gz` | 185,887 | 0 | `Lmax_8` → `a8_9` (113,321) | `vcert2` |
| 2 | `partial/k-stages-1-12-8-9.txt.gz` | 6,602 | 11,148 | 113,321 → 95,571 | `kzv5` |
| 3 | `complete/certs/k8-stage-13.txt.gz` | 0 | 754 | 95,571 → 94,817 | `kzv5` |
| 4 | `complete/certs/k8-seg-A.txt.gz` | 2,704 | 3,620 | 94,817 → 88,493 | `kzv5` |
| 5 | `complete/certs/k8-tail.txt.gz` | 81,380 | 7,112 | 88,493 → `{e_8}` | `kzv5` |

That is 299,207 = `|Lmax_8| − 1` moves in all, 22,634 of them (K). Every (K) move deletes a point `u` with
`|u|_1 = 9` and `u_8 = 0`.

**Piece 1.** `vcert2` replays it from `Lmax_8` in eight chunks of 25,000 lines, chained by `-o`/`-i`.
- It builds the full `l^1` ball and marks `Lmax_8`.
- It checks each domination by exhaustive search.
- Every chunk reports `all moves valid`.
- The final present set equals `cores/K8_9.txt.gz`, the set `a8_9` (sorted comparison).

**Pieces 2–5.** `kzv5` replays each piece from the previous piece's end set, in budgeted runs.
- A run stops only at a line boundary, and the next run continues from the set it wrote, with the remaining lines.
- Every line deletes exactly the point it names. So the start set of any stretch of lines is the piece's start set
  minus the points deleted before the stretch.
- The long pieces were therefore replayed as independent stretches:
  - pieces 2 and 4 stage by stage;
  - piece 5 in four stretches of 1,778 (K) lines each.
- For every stretch, the replayed end set was compared, sorted, with the predicted end set, and they were equal.
- The final stretch ends with `end=1 END={e_k} ACCEPT`.
- `kzv5` also checks that each start set is duplicate-free and lies in `Lmax_8`.

So the concatenation is a lifted certificate on `Lmax_8` at `r = 9` that ends at `{e_8}`.

**How piece 5 was assembled.** This does not affect soundness, which rests only on the replays.
- The 11,170 points `T13` of the stage-13 end set with `|u| = 9` and `u_8 = 0` were split into three lists.
- (K) was searched on each list in parallel, each from an assumed start set.
- Segment A's last stage ended in a (D) cascade, which deleted 2,600 points outside `T13`.
- Piece 5 is segments B and C, with every line whose point was already deleted removed. That is 2,600 lines, all
  (D). No kept line names a deleted `w`.
- It was then re-verified from A's actual end set. The details are in `complete/README.md`.

## 4. Why (K) is needed and where it acts

By `z8-rips-lifted-domination-certificates-fail-at-scale-9`, no certificate for `k = 8, r = 9` uses (D) moves
alone. As at `(8, 8)`, the (K) moves act only on the top shell `|u|_1 = r` with `u_8 = 0`.

After stage 13, deleting all 11,170 such points outright leaves an 83,647-point set. That set collapses by (D)
alone: `kzh` finds the 83,646-move cascade, and `kzv5` accepts it. The certificate of §3 realises this: (K) moves
on those points, interleaved with (D) cascades, and then a final (D) cascade of about 81,000 moves.

## 5. Consequence

`VR(Z^8, d_1; 9)` is contractible, by the Theorem of §1 applied with the certificates of §2 and §3.

---
rg: 2
id: z8-rips-contractible-at-scale-8-proof
kind: route
title: Lifted domination and link-collapse certificates for k = 2..8 at scale 8, replayed by independent verifiers
target: z8-rips-contractible-at-scale-8
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, research/z6-rips-contractible-at-scales-6-to-9-proof.md, experiments/zn-rips-link-collapse-2026-09-18/README.md, experiments/zn-rips-link-collapse-2026-09-18/kz.cpp, experiments/zn-rips-link-collapse-2026-09-18/kze.cpp, experiments/zn-rips-link-collapse-2026-09-18/kzv.cpp, experiments/zn-rips-link-collapse-2026-09-18/kzv3.cpp, experiments/zn-rips-link-collapse-2026-09-18/genL.py, experiments/zn-rips-link-collapse-2026-09-18/replay.sh, experiments/zn-rips-link-collapse-2026-09-18/negK.py, experiments/zn-rips-link-collapse-2026-09-18/stuck-5-4.txt, experiments/zn-rips-link-collapse-2026-09-18/results.txt, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k2.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k3.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k4.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k5.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k6.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k7.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k8-prefix.txt.gz, experiments/zn-rips-link-collapse-2026-09-18/certs/cert-8-8-k8-link.txt.gz, experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp, experiments/zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp]
---

Notation is as in `research/z7-rips-contractible-at-scale-10-proof.md`:
- `N[v]` is the closed neighbourhood at `d_1`-distance `≤ r`;
- `x ≻ 0` means the last nonzero coordinate of `x` is positive;
- `hull(S)` is the smallest integer box containing `S`;
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }` and `E = e_k`.

Here `n = r = 8`.

## 1. The reduction

§1–§3 of `z7-rips-contractible-at-scale-10-proof` hold for every `(n, r)`. They give the following.

**Theorem** (loc. cit.). Suppose that for each `k = 2, …, n` there is a lifted certificate on `Lmax_k` at scale `r`
that ends at `{e_k}`. Then `VR(Z^n, d_1; r)` is contractible.

A lifted certificate is a sequence of moves on a current set `C`, which starts as `Lmax_k`:
- **(D) x | w.** Here `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and `N[x] ∩ C ⊆ N[w]`. Delete `x`.
- **(K) u | w ; (b_1 | v_1), …, (b_m | v_m).** Put `S = N(u) ∩ C`. Each step needs:
  - `b_j, v_j` in the current `S`, with `v_j ≠ b_j`;
  - `v_j ∈ hull(0, u, b_j, E)`;
  - `N[b_j] ∩ S ⊆ N[v_j]`.

  The step removes `b_j` from `S`. At the end we need `w ∈ S`, `w ∈ hull(0, u, E)` and `S ⊆ N[w]`. Then
  delete `u` from `C`.

So it suffices to exhibit seven certificates at `r = 8`, one for each `k = 2, …, 8`.

## 2. Compact K lines

The files here write a (K) move as a single line `K u | w`, without the steps. The verifiers `kzv.cpp` and
`kzv3.cpp` rebuild the steps themselves. They start from `S` = the present points `z ≠ u` with `d(z, u) ≤ r`.
Then they repeatedly pick some `b ≠ w` in the current `S` and some `v` in the current `S` with:
- `v ≠ b` and `d(b, v) ≤ r`;
- `v ∈ hull(0, u, b, E)`, checked coordinatewise;
- `N[b] ∩ S ⊆ N[v]`, checked on bit rows built from explicit `d_1` distances.

Each such `b` is removed. The verifier accepts the line only if, at the end, every point of the current `S` is
within `r` of `w`. It also checks `w ≠ u`, `d(u, w) ≤ r` and `w ∈ hull(0, u, E)`. Since `w` is never removed,
`w ∈ S` at the end.

The steps it performs are exactly steps `(b_j | v_j)` as in §1. So each accepted compact line, together with the
verifier's run on it, is a (K) move in the sense of the Theorem. Soundness does not depend on the order in which the
verifier picks `b` and `v`, because every step it takes is checked.

(D) lines are checked in the same way: `x, w` present, `w ≠ x`, `d(x, w) ≤ r`, `w ∈ hull(0, x, E)`, and
`N[x] ∩ C ⊆ N[w]` on the bit rows. The verifiers check that the start file lies in `Lmax_k` and has no
duplicates. They check its size against `|Lmax_k| = (Σ_i 2^i C(k,i) C(r,i) − 1)/2`, so it is all of `Lmax_k`.

## 3. The certificates

All files are in `experiments/zn-rips-link-collapse-2026-09-18/certs/`.

| k | `|Lmax_k|` | D-moves | K-moves | K link steps | verifier | end |
|---|---|---|---|---|---|---|
| 2 | 72 | 71 | 0 | 0 | `kzv`, `kzv3` ACCEPT | `{e_2}` |
| 3 | 416 | 415 | 0 | 0 | `kzv`, `kzv3` ACCEPT | `{e_3}` |
| 4 | 1,824 | 1,823 | 0 | 0 | `kzv`, `kzv3` ACCEPT | `{e_4}` |
| 5 | 6,536 | 6,535 | 0 | 0 | `kzv`, `kzv3` ACCEPT | `{e_5}` |
| 6 | 20,040 | 20,039 | 0 | 0 | `kzv`, `kzv3` ACCEPT | `{e_6}` |
| 7 | 54,272 | 53,599 | 672 | 2,427,964 | `kzv`, `kzv3` ACCEPT | `{e_7}` |
| 8 | 132,864 | 92,422 + 35,289 | 5,152 | 38,604,900 | `vcert2` + `kzv3` ACCEPT | `{e_8}` |

For `k ≤ 7` one file `cert-8-8-k<k>.txt.gz` holds the whole certificate. It was found by `kz.cpp`
(`./kz k 8 L.txt core.txt cert.txt`, with `L.txt` from `python3 genL.py k 8 L.txt`). It is replayed from all of
`Lmax_k` by `kzv.cpp` (`./kzv k 8 L.txt cert.txt`) and again by `kzv3.cpp`. The link-step column counts the steps `kzv`
performs. `kzv3` picks steps in a different order and performs 2,381,660 at `k = 7`.

For `k = 8` the certificate is the concatenation of two files.
- **Prefix.** `cert-8-8-k8-prefix.txt.gz` has 92,422 moves. They are 56,064 lines tagged `A` and 36,358 lines
  tagged `D`, and all of them are plain (D) moves. It is the deterministic output of
  `experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp` (`./ilv4 8 8 cert.txt - end.txt 1100 400`).
  `vcert2.cpp` from the same directory replays it from `Lmax_8`: it builds the full `l^1` ball, marks `Lmax_8`, and
  checks each domination by exhaustive search. It reports `start present=132864 (= |Lmax|)`, `all moves valid` and
  `left=40442`. Its end set is the 40,442-point set `a8_8`, which is D-stuck.
- **Link part.** `cert-8-8-k8-link.txt.gz` has 40,441 compact lines, 35,289 `D` and 5,152 `K`. It takes `a8_8` to
  `{e_8}`. It was found by `kz.cpp` (the first 2,908 K lines) and `kze.cpp` (the rest), in four budgeted stages.
  `kzv3.cpp` replays it from `a8_8`. Each run is budgeted and stops only at a line boundary. The next run starts
  from the set the previous run wrote and continues with the remaining lines. So together the runs check every
  line in order. The replay took 1,770 CPU seconds in 13 pieces, and each of the four search stages ended exactly
at the start set of the next.

`results.txt` records the sha256 of every certificate, every replay log line, and the stage boundaries.

**Why K is needed.** By `z8-rips-lifted-domination-certificates-fail-at-scale-8`, no certificate for `k = 8,
r = 8` uses (D) moves alone. Here the first 2,140 K moves all delete norm-8 points of the D-stuck set `a8_8`. In
total 5,152 K moves suffice, all on norm-8 points. They release (D) cascades that empty every lower shell.

## 4. Controls

- On the 30-point set `stuck-5-4.txt`, a D-stuck set at `(k, r) = (5, 4)`, both verifiers reject every single move:
  all 228 admissible `D u | w` lines and all 228 admissible `K u | w` lines.
- In a `(6, 6)` certificate with 80 K lines, these corruptions are all rejected:
  - replacing a K line's `w` by a point outside `hull(0, u, E)`;
  - deleting one K line;
  - changing a K tag to D;
  - swapping in a non-dominating `w` on a D line;
  - a truncated file;
  - dropping one point from the start set.

  Swapping in a different but valid dominator is accepted, as it should be.
- The `(7, 7)` certificate from `kze.cpp` (D = 23,190, K = 1,128) is accepted by both `kzv` and `kzv3`.

## 5. Consequence

`VR(Z^8, d_1; 8)` is contractible, by the Theorem of §1 applied with the seven certificates of §3. This is the
sharp scale `r = n` for `n = 8`. Before this, `n = 8` was known only for `r ≥ 37` and even `r ≥ 20`.

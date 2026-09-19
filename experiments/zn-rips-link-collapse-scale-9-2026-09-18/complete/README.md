# VR(Z^8, d_1; 9): the complete lifted certificate

This finishes the partial certificate in `../partial/`. It is used by
`research/z8-rips-contractible-at-scale-9-proof.md`. Here `Lmax_8` at `r = 9` has 299,208 points and `E = e_8`.

## The k = 8 certificate, in order

The certificate is the concatenation of these pieces. Each piece starts from the set where the previous one ends.

| # | file | lines | D | K | start → end |
|---|---|---|---|---|---|
| 1 | `../partial/d-prefix-8-9.txt.gz` | 185,887 | 185,887 (`A`/`D`) | 0 | `Lmax_8` (299,208) → `a8_9` (113,321) |
| 2 | `../partial/k-stages-1-12-8-9.txt.gz` | 17,750 | 6,602 | 11,148 | 113,321 → 95,571 |
| 3 | `certs/k8-stage-13.txt.gz` | 754 | 0 | 754 | 95,571 → 94,817 (`sets/end-stage-13.txt.gz`) |
| 4 | `certs/k8-seg-A.txt.gz` | 6,324 | 2,704 | 3,620 | 94,817 → 88,493 (`sets/end-seg-A.txt.gz`) |
| 5 | `certs/k8-tail.txt.gz` | 88,492 | 81,380 | 7,112 | 88,493 → `{e_8}` |

In total there are 299,207 = |Lmax_8| − 1 moves. Of these, 22,634 are (K) moves, and every one of them deletes a
point `u` with `|u|_1 = 9` and `u_8 = 0`.

## How it was found

- **Piece 1** comes from `ilv4`, and **piece 2** from `kze`/`kzf`. Both are described in `../README.md`.
- **Piece 3** comes from `kzh.cpp`, run as `KZ_KFIRST=1 KZ_KSEL=1 ./kzh 8 9 e12.txt e13.txt k13.txt 1100`.
  - `kzh` is `kzf` with search-order switches only: `KZ_KFIRST` skips the opening D-only sweep, `KZ_KSEL` tries
    (K) only at `|u| = r`, `u_n = 0`, and `KZ_KLIST=file` tries (K) only at the listed points.
  - The moves and the certificate format are unchanged.
- **Prediction.** `sets/T13.txt.gz` holds the 11,170 points of the stage-13 end set with `|u| = 9` and `u_8 = 0`.
  Deleting all of them leaves 83,647 points. From there `kzh` finds a pure D cascade of 83,646 moves down to
  `{e_8}`, and `kzv5` accepts it. This pointed to a certificate made of K moves on `T13` followed by a D cascade.
- **Segments.** `T13` was cut into three parts: lines 1–3,724 (A), lines 3,725–7,448 (B) and lines 7,449–11,170 (C).
  - Each part was searched in parallel by `segchain.sh`, with `KZ_KLIST` set to that part.
  - Each search started from the stage-13 end set minus the earlier parts.
- **Joining the segments.**
  - Segment A ended with a D cascade. It deleted 2,704 points, 2,600 of them outside `T13`, so B's assumed start
    set was not reached.
  - The tail piece 5 is therefore built from B's and C's lines: B stages 1–5, with B stage 5 cut after its 130
    (K) lines, then C stages 1–3, keeping them in order.
  - Every line whose point is already gone from A's actual end set is dropped. That is 2,600 lines, all of them (D).
  - None of the kept lines has its `w` missing.
  - The kept lines were then replayed from A's actual end set. This works for two reasons. A (D) move stays valid
    when `C` shrinks, provided `x` and `w` are present. A (K) move is re-checked by the verifier on the smaller link.

## How it is checked

- **Piece 1:** `vcert2` of `../../zn-rips-lifted-domination-core-2026-09-18/` replays it from `Lmax_8` in 25,000-line
  chunks, using `-i`/`-o`. All moves are valid. The end set equals `../cores/K8_9.txt.gz` exactly.
- **Pieces 2–5:** `kzv5` (in `..`) replays them in budgeted runs, driven by `vpiece.sh`. A piece's start set is the
  previous end set. Each line deletes exactly its named point, so the start set of any sub-piece is determined:
  it is the piece's start minus the points deleted earlier.
  - This lets the long pieces be replayed as independent sub-pieces.
  - Every sub-piece's replayed end set is compared, sorted, with its predicted end set.
  - The last sub-piece ends at `{e_8}` with `END={e_k} ACCEPT`.
- **k = 2..7:** `certs/cert-9-k<k>.txt.gz` start from `L<k>.txt`, which is `../../zn-rips-link-collapse-2026-09-18/genL.py k 9`.
  They are replayed by `kzv5` (start is all of `Lmax_k`, end `{e_k}`) and by `kzv3` of the (8,8) directory.

`results.txt` has every log line and the sha256 of every file.

## (8,10): implicit adjacency (`kzs.cpp`)

`kzs` is `kzh` with no `M × M` bit matrix.
- Every neighbourhood is recomputed with `vpsadbw` from packed coordinates (`byte = coordinate + 64`).
- A dead point is packed as all-ones, so it is never within `r` of anything.
- Link rows are built the same way inside the link.
- Memory is `O(M + s²/8)` for a link of size `s`.
- On `a8_8`, `kzs` makes exactly the same moves as `kzh`, as a certificate prefix (see `results.txt`).

At `(8, 10)`, `kzs` ran on the 205,606-point set left by two `ilv4` stages from `Lmax_8` (628,232 points). That
set is time-budgeted and is not a D-stall set.
- It used about 200 MB RSS.
- It made 137 (K) moves in 1,106 s wall at about 20% of one core, which is about 1.6 CPU-s per (K).
- That set holds 18,816 points with `|u| = 10` and `u_8 = 0`.

If `(8, 10)` follows the `(8, 9)` pattern, the (K) phase costs about 8 CPU-hours, and can be run as parallel
segments.

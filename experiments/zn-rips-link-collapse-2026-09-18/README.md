# Lifted link-collapse certificates for VR(Z^8, d_1; 8)

This directory backs the route `research/z8-rips-contractible-at-scale-8-proof.md`. The reduction (lifted peeling
links, one certificate per link dimension `k`, each ending at `{e_k}`) is §1–§3 of
`research/z7-rips-contractible-at-scale-10-proof.md`.

At `(k, r) = (8, 8)` domination moves alone get stuck
(`research/z8-rips-lifted-domination-certificates-fail-at-scale-8.md`). The certificate here adds link-collapse
(K) moves. It needs 5,152 of them, all on points of norm 8, and they release (D) cascades that empty the rest.

Everything is single-threaded C++17. `kzv.cpp`, `kzv3.cpp`, `kz.cpp` and `kze.cpp` use `_pext_u64`, so build them
with `g++ -O2 -march=native` on an x86-64 machine with BMI2.

## Files

| file | role |
|---|---|
| `genL.py` | `python3 genL.py k r out.txt` writes `Lmax_k` at scale `r`, one point per line. |
| `kz.cpp` | Search. It runs (D) sweeps, then (D)+(K) sweeps in order of decreasing norm, and writes compact lines `D x \| w` and `K u \| w`. Usage: `./kz k r start.txt end.txt cert.txt [budgetSec]`. It produced the certificates for `k ≤ 7` and the first two stages at `k = 8`. |
| `kze.cpp` | The same search with a faster link collapse: it tries lattice-neighbour dominators first and stops early. It produced stages 3 and 4 at `k = 8`. |
| `kzv.cpp` | Verifier. It shares no code with the search. Usage: `./kzv k r start.txt cert.txt [end.txt]`. |
| `kzv3.cpp` | The same checks as `kzv.cpp`, with a faster collapse and an optional wall-clock budget. Usage: `./kzv3 k r start.txt cert.txt [end.txt] [budgetSec]`. On budget it stops at a line boundary, writes the current set and exits 3. |
| `replay.sh` | Rebuilds and replays everything, including the prefix with `../zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp`. |
| `negK.py`, `stuck-5-4.txt` | Negative control: every single admissible move on a stuck set must be rejected. |
| `results.txt` | Logs, stage boundaries and sha256 sums. |
| `certs/` | The certificates, gzipped. |

## What the verifiers check

`kzv` and `kzv3` read a start set. They check that it is a duplicate-free subset of `Lmax_k` that contains `e_k`,
and print whether it is all of `Lmax_k`, by comparing its size with `(Σ_i 2^i C(k,i) C(r,i) − 1)/2`. They build
closed-neighbourhood bit rows from explicit `l^1` distances. Then they check each line in order:

- `D x | w`:
  - `x` and `w` present, `w ≠ x`, `d(x, w) ≤ r`;
  - `w ∈ hull(0, x, e_k)`;
  - `N[x] ∩ C ⊆ N[w]`.

  Then `x` is deleted.
- `K u | w`:
  - `u` and `w` present, `w ≠ u`, `d(u, w) ≤ r`;
  - `w ∈ hull(0, u, e_k)`.

  Put `S = N(u) ∩ C`. The verifier repeatedly removes some `b ≠ w` for which there is a `v` in the current `S`
  with `v ≠ b`, `d(b, v) ≤ r`, `v ∈ hull(0, u, b, e_k)` and `N[b] ∩ S ⊆ N[v]`. It accepts if at the end every
  point of `S` is within `r` of `w`. Then `u` is deleted.

Every removal is checked, so the run is an explicit (K) move with steps `(b_j | v_j)`, whatever order the
verifier uses. At the end the verifier reports whether the present set is exactly `{e_k}`.

## Certificates

| file | k | start | lines | end |
|---|---|---|---|---|
| `cert-8-8-k2.txt.gz` … `cert-8-8-k7.txt.gz` | 2..7 | `Lmax_k` | see `results.txt` | `{e_k}` |
| `cert-8-8-k8-prefix.txt.gz` | 8 | `Lmax_8` (132,864) | 92,422 (A/D, all plain (D)) | `a8_8` (40,442) |
| `cert-8-8-k8-link.txt.gz` | 8 | `a8_8` | 40,441 (35,289 D, 5,152 K) | `{e_8}` |

The prefix is the deterministic output of `ilv4.cpp` (`./ilv4 8 8 c8_8.txt - a8_8.txt 1100 400`) in the sibling
directory `zn-rips-lifted-domination-core-2026-09-18`. It is checked by that directory's exhaustive verifier
`vcert2.cpp`.

The link part was searched in four budgeted stages, each started from the previous stage's end set:

| stage | engine | start | D | K | end |
|---|---|---|---|---|---|
| 1 | `kz` | 40,442 | 0 | 2,140 | 38,302 |
| 2 | `kz` | 38,302 | 1,510 | 768 | 36,024 |
| 3 | `kze` | 36,024 | 721 | 1,241 | 34,062 |
| 4 | `kze` | 34,062 | 33,058 | 1,003 | 1 |

`certs/cert-8-8-k8-link.txt.gz` is the concatenation of the four stage files.

## Replay

Run `bash replay.sh` from this directory. The two long steps are the prefix (`vcert2`, a few minutes) and the link
part (`kzv3`). The link part took 1,770 CPU seconds here and runs in pieces of `BUDGET` wall seconds, 800 by default.

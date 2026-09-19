# Lifted certificate at (8, 11): domination pieces around the top shell, and an independent (K) checker

Node: `research/z8-rips-scale-11-reduces-to-top-shell-link-collapses.md` (claim) and its `-proof` route.
All runs are in `results.txt`, with sha256 of the inputs. Machine: 4 cores under load ~20, every run
`nice -n 10 timeout 1200`, single-threaded, below 2 GB.

## Files

| file | what |
|---|---|
| `sets/O-8-11.txt.gz` | `O`, 399,702 points, sorted (`LC_ALL=C sort`) |
| `sets/T-8-11.txt.gz` | `T`, 53,312 points, sorted |
| `certs/d-prefix-8-11.txt.gz` | 843,210 (D) lines, `Lmax_8 → O` (`A`/`D` format of `vcert2`) |
| `certs/d-tail-8-11.txt.gz` | 346,389 (D) lines, `O ∖ T → {e_8}` |
| `certs/k-sample-8-11.txt.gz` | 21 `K` lines at points of `T` and 432 `D` lines, from `C = O` (not used by the claim) |
| `certs/k-formula-single-8-11.txt.gz` | 24 lines `K u \| e_j + e_8`, each checked alone from `C = O` |
| `certs/k-formula-chain-8-11.txt.gz` | 40 such lines, checked in order from `C = O` |
| `ilv5.cpp` | `ilv4` (main, `zn-rips-lifted-domination-core-2026-09-18`) with a resumable pass position |
| `topshell11.py` | part (2) of the claim |
| `vchain.sh`, `vtail.sh` | `vcert2` replays of the prefix and the tail |
| `tail.sh` | how the tail was searched (`KZ_DONLY=1 kzs2`, budgeted pieces) |
| `classtest.sh` | restores one profile class of `T` to `O ∖ T` and runs (D) only (§ "Is T minimal") |
| `kzc1.cpp`, `kzc1-stages.sh` | the independent (K)/(D) checker and its replay of the kzs3 stages of (8, 10) |

## The prefix

`ilv4 8 11` from `Lmax_8` (1,242,912 points) gave stages 1–3 (371,240, 10,061 and 558 lines). A restarted `ilv4`
begins each pass at the start of its order, where the norm-11 points fail again. Stage 3 spent its whole budget
re-failing them. `ilv5` stores the pass position on budget exit (8th argument, a state file `pass pos`) and resumes
there, so stages 4–6 deleted 202,821, 239,795 and 18,735 points. The prefix was stopped after stage 6, at
`O = o6` (399,702 points). `O` is not (D)-stuck. It is only the point where the prefix stops, and the tail does the
rest.

## The top shell

At `(8, 10)` the survivors that needed (K) were the norm-10 points with `x_8 = 0` whose magnitude profile is an
unbalanced partition of 10 with fewer than 8 parts. The prediction for `(8, 11)` was the same set at norm 11. The
unbalanced partitions of 11 with fewer than 8 parts are
`(5,1^6), (4,2,1^5), (3,3,1^5), (3,2,2,1^4), (2^4,1^3), (4,2,2,1^3), (3,3,2,1^3), (3,2,2,2,1,1)`.

`{ x ∈ O : |x|_1 = 11, x_8 = 0 }` has 53,360 points: every point of the last seven classes (53,312), and 48 points
of `(5,1^6)`. Those 48 are an artifact of the order in which the prefix stopped. With them put back into `O ∖ T`,
the (D)-only search still reaches `{e_8}` (the tail here). So `T` is the seven complete classes.

## Is `T` minimal?

`classtest.sh P` puts one class back and runs (D) only. A class that is then deleted too need not be in `T`. At
load ~20 the first class, `(3,2,2,2,1,1)`, was still far from done after two 1100 s pieces, so the test was stopped
(`results.txt`). Whether `T` is minimal is open. The (K) phase does not need it.

## The (K) phase at (8, 11)

`certs/k-sample-8-11.txt.gz` came from `KZ_KFIRST` `kzs2` on 21 points of `T` against `C = O`: all 21 (K) moves
succeed, in 900 s wall at about 20% of a core. The witnesses:
- `w = e_7 + e_8` for 13 of the 18 sample points with `x_7 ≠ 0`;
- for the other 8 (the 3 with `x_7 = 0` and 5 more), `w = u' + e_8`, where `u'` is `u` with its largest `|u_i|`
  (sometimes several coordinates) moved towards 0. In 4 cases this is `u − sgn(u_i) e_i + e_8`, of norm 11.
The search tries candidates in its own order, so this says which witness it found first, not which ones work.

`kzc1` checks a formula line `K u | e_j + e_8` (`j` = last nonzero index of `u`) against `C = O` in 4–13 s. It
accepted 24 of 24 random single lines (`certs/k-formula-single-8-11.txt.gz`) and a 40-line sequential chain
(`certs/k-formula-chain-8-11.txt.gz`). See `results.txt`, section "formula witnesses". With that cost, the whole (K) phase is about 53,312 × 8 s ≈ 120
core-hours of checking, so it needs splitting across lanes. The block-chain join rule of `z8-rips-contractible-at-scale-10`
applies unchanged.

## `kzc1`: an independent checker for (K) lines

The (8, 10) certificate of `z8-rips-contractible-at-scale-10` has 987 (K) lines from the block-restricted search
`kzs3`. They were replayed only by `kzv7`, which shares parsing and distance code with `kzs3`. `kzc1.cpp` is written
from the definitions and shares no code with `kzs2`, `kzs3`, `kzv6`, `kzv7` or `vcert2`:
- its own tokenizer, and a rank table instead of their hash;
- `l^1` distances by byte-column differences (structure of arrays), with no SIMD sum-of-absolute-differences;
- (D) checked by an explicit scan of the current set;
- (K) checked by collapsing the link `N(u) ∩ C` (bit rows, with prefix-union box filters for the hull) until it is a
  cone on `w`. Every removal is re-checked with explicit distances, and a final explicit test requires every point
  left in the link to be within `r` of `w`.

`kzc1 k r Ofile certfile first last endfile` replays lines `first..last` and writes the end set. `kzc1-stages.sh`
replays the six kzs3 stages `E2, E3, E4, F2, F3, F4` of (8, 10) in 12-line chunks, each from the end set of the
previous chunk. It compares the sorted end set of each stage with the one recorded by w9-103. The outcome is in
`results.txt`.

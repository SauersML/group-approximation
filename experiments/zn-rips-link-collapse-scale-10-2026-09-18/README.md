# VR(Z^8, d_1; 10), k = 8: the domination parts and the top-shell set

This directory is used by `research/z8-rips-scale-10-reduces-to-top-shell-link-collapses-proof.md`. At `r = 10`,
`Lmax_8` has 628,232 points, and `E = e_8`. The certificates for `k = 2..7` at `r = 10` are already on main, in
`../zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k<k>.txt.gz`. So `(8, 10)` needs only the `k = 8`
certificate.

Build: `g++ -O2 -march=native -o X X.cpp`. `kzs2` needs AVX-512BW, and `kzv6` needs AVX2. `ilv4` and `vcert2` are the
copies in `../zn-rips-lifted-domination-core-2026-09-18/`.

## The pieces

| piece | file | lines | start → end | checked by |
|---|---|---|---|---|
| (1) | `certs/d-prefix-8-10.txt.gz` | 442,086 (D) | `Lmax_8` (628,232) → `O` (186,146) | `vcert2` |
| (3) | `certs/d-tail-8-10.txt.gz` | 167,329 (D) | `O ∖ T` (167,330) → `{e_8}` | `vcert2`, `kzv6` |

- `sets/O-8-10.txt.gz` is `O`, sorted.
- `sets/T-8-10.txt.gz` is `T = { x ∈ O : |x|_1 = 10, x_8 = 0 }`, which has 18,816 points.
- `topshell.py` checks that `T` is exactly the set of norm-10, `x_8 = 0` points of `Lmax_8` whose nonzero `|x_i|`
  form a 7-part partition of 10 or the partition `(3,2,2,1,1,1)`.
- To make the start set of (3): `zcat sets/O-8-10.txt.gz sets/T-8-10.txt.gz | sort | uniq -u > OminusT.txt`.

The missing middle piece takes `O` to `O ∖ T`. Once it exists, (1), then that piece, then (3) is the `k = 8`
certificate. It is partly built; see the (K) phase below.

The D-stall set `A` of `O` is `sets/stall-8-10.txt.gz` (186,074 points). `certs/d-stall-8-10.txt.gz` has the 72 (D) lines
from `O` to `A`, and `kzv6` accepts them. `A` still contains all of `T`.

## How the pieces were found

1. **`ilv4`, one 1,100 s stage from `Lmax_8`.** It was stopped by its budget in its second (D) pass, after 356
   deletions in that pass. Its end set is `O`.
2. **`KZ_DONLY=1 kzs2` from `O`.** It found only 72 more (D) moves, all at norm 10 with `x_8 > 0`. They are not used.
   The resulting 186,074-point set is the D-stall set `A`; the check that it really is a stall is in `results.txt`.
3. **The prediction test.** Delete the 18,816 points of `T` from `O`, and run `KZ_DONLY=1 kzs2` from the rest. The
   (D) sweep reaches `{e_8}` in one pass, in 194 s. That is piece (3). So at `(8, 10)`, as at `(8, 8)` and
   `(8, 9)`, only top-shell points with `x_8 = 0` block domination.

`T` is a union of whole classes, one class for each magnitude profile. Every point of `Lmax_8` with one of the
listed profiles survives in `O`. No other norm-10 point with `x_8 = 0` survives.

For comparison, look at the `(8, 9)` D-stall set of w6-103 (113,321 points). Its norm-9, `x_8 = 0` survivors
number 23,072, and three kinds of profile occur among them:
- `(3,2,2,1,1)`;
- the 6-part partitions of 9 other than `(4,1^5)`;
- both 7-part partitions of 9.

So going from `r = 9` to `r = 10`, the minimum support of a survivor rises from 5 to 6.

## Tools

- **`kzs2.cpp`** is the search: `kzs` of w7-103, with AVX-512 neighbourhoods and link rows (8 packed points per
  `vpsadbw`).
  - It takes `KZ_KFIRST=1`, `KZ_KSEL=1` (try (K) only at `|u| = r`, `u_n = 0`) and `KZ_KLIST=file` (try (K) only at
    the listed points).
  - `KZ_DONLY=1` stops after the (D) sweeps.
  - On the 205,606-point `(8, 10)` set of w7-103, its certificate is a prefix of `kzs`'s.
- **`kzv6.cpp`** is the verifier. It shares no code with the searches.
  - It is `kzv5` without the global `M × M` bit matrix: neighbourhoods and link rows are recomputed from packed
    coordinates.
  - It uses the same (D) check and the same maximal protected collapse for (K).
  - `./kzv6 k r start cert [out] [budgetSec]`: with a budget it exits 3 with `PAUSED`.
- **`vpiece6.sh`** replays a certificate with `kzv6` in budgeted pieces and compares the end set with a predicted one.
- **`segchain.sh`** runs one (K) block chain as chained 1,100 s `kzs2` stages.
- **`vloop.sh X`** replays the finished stages of chain `X` in order with `vpiece6.sh`.
- **`stageseg.sh`** collects the finished stages into `segments/` and checks the join condition below.

## The (K) phase: deleting `T` from `O` (partial)

`T` is split into four blocks of 4,704 points, `segments/TA.txt.gz` to `segments/TD.txt.gz`. They partition `T`.
Block `X` is searched by its own chain, with K tried only at points of that block
(`KZ_KFIRST=1 KZ_KSEL=1 KZ_KLIST=TX.txt kzs2`, see `segchain.sh`). Each chain starts from a different set:

| chain | start set | size |
|---|---|---|
| A | `O` | 186,146 |
| B | `O ∖ TA` | 181,442 |
| C | `O ∖ (TA ∪ TB)` | 176,738 |
| D | `O ∖ (TA ∪ TB ∪ TC)` | 172,034 |

**Join rule.** Every line of every chain so far is a (K) line at a point of the chain's own block. `stageseg.sh`
checks this: no `D` lines, and no deleted point outside the block. Suppose chain A finishes its block. Then it ends
at exactly `O ∖ TA`, which is the start set of chain B, and likewise for C and D. When all four blocks are finished,
the `k = 8` certificate is `d-prefix`, then chains A, B, C and D, then `d-tail`, with nothing searched again.

**Status when staged** (10 stages of 1,100 s per chain):

| chain | (K) lines | block points left | end of the chain | stages replayed by `kzv6` (lines) | sha256 of `segments/k-segX-8-10.txt.gz` |
|---|---|---|---|---|---|
| A | 4,118 | 586 | 182,028 | 1–2 (915) | `f8cd7f3c…` |
| B | 2,965 | 1,739 | 178,477 | 1–2 (655) | `bced1f00…` |
| C | 3,455 | 1,249 | 173,283 | 1–2 (573) | `eee304ce…` |
| D | 4,704 | **0** | 167,330 = `O ∖ T` | 1 (429) | `031f17f0…` |

In total 15,242 of the 18,816 points of `T` are deleted, and 3,574 are left, all in blocks A, B and C. 2,572 of the
lines are replayed by `kzv6`.

**Chain D is finished.** It deletes all of `TD` by (K), and its end set equals `O ∖ T` exactly (checked with `sort`
and `cmp` against the start set of `d-tail`). The search went on in its tenth stage with 97,828 (D) moves from
`O ∖ T`, which removed every norm-10 point. Those moves are not kept, because `d-tail` already covers that step.
So `(8, 10)` now needs only chains A, B and C to finish their blocks.

**Verification tiers.**
- *Verified:* the stages listed as replayed. `kzv6` (through `vpiece6.sh`) replayed each of them from its start set
  and reached exactly the end set of the search.
- *Search tier:* the remaining stages have been checked only by `kzs2` itself.
- The start sets of chains B, C and D are predictions. They become the true states only once the earlier chains
  finish their blocks.

`kzv6` is about 2 to 3 times slower per line than the search (about 1.5 to 4 s of CPU per (K) line on this host), so its replay lags
behind the search.

**To continue chain `X`.** Its current set is its start set minus the first point of every line of
`segments/k-segX-8-10.txt.gz`. Save that set as `sX_<n>.txt`, where `n` is the number of stages done, next to
`TX.txt`, and run `./segchain.sh X <n+1>`.

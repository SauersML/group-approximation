---
rg: 2
id: f2-cayley-sse-exact-census-small-k
kind: claim
title: Exact small-set expansion of weighted Cayley graphs of F_2^k for k <= 7 -- subcubes are exactly optimal in the noisy cube, the basic SDP is off by 0.004-0.015 at s = 8 and pure spectral certificates by about 0.1, and Cay(F_2^7, weight <= 2) has a non-subgroup optimum where the SDP is tight
distinct_from:
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that is a theorem for all k; this is a certified finite census (exact values by branch and bound) that calibrates it and supplies its extremal witnesses.
  small-set-expansion-hypothesis: that is the open hardness statement; this is a finite computation on small Cayley instances.
artifacts:
  - experiments/sse-small-instances-2026-09-17/run_census.py
  - experiments/sse-small-instances-2026-09-17/sse_cayley.py
  - experiments/sse-small-instances-2026-09-17/sse_exact.c
  - experiments/sse-small-instances-2026-09-17/search_gaps.py
  - experiments/sse-small-instances-2026-09-17/subgroup_dominance.py
  - experiments/sse-small-instances-2026-09-17/linear_gap_lp.py
---

**OPEN** (computational). The census was run on 2026-09-17 and its certified
replay is kept as an attempt (see Attempts). It is not established because the
lane's referee stage recorded no verdict on it: no referee refuted it, and no
referee read it. The replay `python3 run_census.py` exits 0 only if every number
below is reproduced, but nobody has independently audited the branch-and-bound
pruning bound that makes the EXACT values exact.

*Quantities.* `stay(S) = 1 - Phi(S)` on `Cay(F_2^k, w)`. At `|S| = s`:

- **EXACT** is `max_S stay(S)`, computed by the integer branch and bound `sse_exact.c`.
- **SUB** is the best subgroup.
- **SDP** is the translation-symmetrised basic SDP. For Cayley graphs this is
  the Delsarte LP over `g(x) = |S n (S+x)|/N` with `ghat >= 0`; averaging an
  optimal Gram matrix over translations loses nothing.
- **EIG** is the best pure spectral certificate
  `delta sum_(i<m) lambda_i + (1 - m delta) lambda_m` with `m = floor(1/delta)`.
  It dominates the threshold-rank bound `lambda_(r+1) + r delta`.

**(A) Noisy cube.** Weights `rho^|a| (1-rho)^(k-|a|)`, with `rho` in
`{1/8, 1/4, 3/8}`. The cases are `k = 4` at `s <= 8`, `k = 5` at `s <= 16`, and
`k = 6, 7` at `s <= 8`. In all 39 cases EXACT = SUB: subcubes are exactly optimal.
At `s = 8`:

| `k` | `rho` | EXACT | SDP | EIG |
|---|---|---|---|---|
| 6 | 1/8 | 0.401170 | 0.411260 | 0.560621 |
| 6 | 1/4 | 0.296703 | 0.306801 | 0.429759 |
| 6 | 3/8 | 0.196232 | 0.200394 | 0.277232 |
| 7 | 1/8 | 0.318598 | 0.333577 | 0.459702 |
| 7 | 1/4 | 0.211101 | 0.219741 | 0.314785 |
| 7 | 3/8 | 0.119798 | 0.123512 | 0.172290 |

So the basic SDP overestimates by `0.004` to `0.015` at `s = 8`, while EIG
overestimates by `0.08` to `0.14`. The pure spectral certificate is the furthest
from the truth, and it grows looser as `k` grows at fixed `s`.

**(B) Non-subgroup optimum.** In `Cay(F_2^7, all a with |a| <= 2)` at `s = 8`:

- EXACT = SDP = `1/4`, attained by the Hamming ball `{0, e_1, ..., e_7}`;
- every 3-dimensional subgroup has stay at most `3/14`.

So subgroups are not always exactly optimal, but here the basic SDP is exact.
This is the low-stay regime (`Phi = 3/4`), and the subgroup loss in `Phi` is the
factor `(11/14)/(3/4) = 22/21`.

**(C) Size 4.** Exact s = 4 optimum = best 2-dimensional subgroup on 40 random
integer-weighted Cayley graphs (`k = 5, 6`). This is a regression check of the
four-lines argument in `f2-cayley-subgroup-sets-are-constant-factor-optimal`,
which proves it for all weights and all `k`.

**(D) SDP gaps on unweighted generator sets** (from `search_gaps.py`: 400
samples at `k = 5`, 150 at `k = 6`).

| `k` | `D` | `s` | EXACT | SDP |
|---|---|---|---|---|
| 5 | {9,18,26,27,28,31} | 6 | 1/2 | 7/12 |
| 5 | {14,15,17,24,25,26,29} | 4 | 2/7 | 1/3 |
| 6 | {5,12,16,30,40,42,53,61} | 4 | 1/4 | 7/24 |
| 6 | {1,10,25,34,48,56,60} | 8 | 3/7 | 13/28 |

No non-subgroup optimum appeared in those samples at power-of-two sizes.

**(E) Subgroup-dominance constants.**

- `max C(S) = 1` over all 6435 sets at `(k, s) = (4, 8)`.
- `C(ball_7) = 22/21`.
- The local-search witnesses give `52/51` at `(5, 8)`, `22/21` at `(6, 8)` and
  `70/69` at `(6, 16)`.

**(F)** Exact rational checks of the spectral-sampling theorem.

*Anomalies reported.*

- (B) is the only non-subgroup optimum found.
- The largest subgroup loss found anywhere is `22/21`, far below the proved
  `E_c/2`.
- Earlier k = 5 runs of the adversarial-weight LP `linear_gap_lp.py` found ratio
  `1.0` at `eta = 0.2` (subgroups of size 8) and `0.667` (sizes 8 and 16). Many
  random starts were infeasible.
- The `k = 7, s = 16` and `k = 8` noisy-cube runs did not finish in the time
  available and are not claimed.

## Attempts

1. **Certified replay by integer branch and bound (2026-09-17, wave
   `swarm-0917`; ran clean, never refereed).** Formerly route
   `f2-cayley-sse-exact-census-small-k-proof`, `requires: []`. The replay
   argument is kept as the attempt artifact
   `research/artifacts/f2-cayley-sse-exact-census-small-k-proof-2026-09-17.md`,
   together with `experiments/sse-small-instances-2026-09-17/{run_census.py,
   sse_exact.c, sse_cayley.py, subgroup_dominance.py, search_gaps.py,
   linear_gap_lp.py}`.

   - *Reason it is not established.* The lane wrote it as ESTABLISHED, but its
     referee stage returned no verdicts at all — the votes were lost, not cast
     against it. A computational claim whose certificate no referee has read is
     agent-written, not agent-verified, so the claim returns to OPEN and the
     replay lands as an attempt. **No referee found an error**; none looked.
   - *What is unaudited.* Every EXACT value rests on the admissibility of the
     pruning bound in `sse_exact.c`: if that bound can ever exceed the true
     completion value, the search may prune an optimum and the census silently
     reports a lower number. The artifact argues the bound is admissible; nobody
     has checked that argument. The SDP, EIG, subgroup and dominance values do
     not depend on it, since they come from enumeration and from linear programs.
   - *What still holds independently.* `python3 run_census.py` exits 0 only if
     every number above reproduces, so the numbers are at least reproducible from
     the committed code. The 39 noisy-cube cases, the `Cay(F_2^7, |a| <= 2)`
     non-subgroup optimum, and `max C(S) = 1` over all 6435 sets at `(k, s) =
     (4, 8)` are the load-bearing outputs.
   - **To restore:** have a referee audit the pruning bound of `sse_exact.c` and
     re-run the replay, then restore the artifact as a route with `target` and
     `requires: []` unchanged.

---
rg: 2
id: fpbs-tree-projected-vertical-slot-second-moment
kind: claim
title: Vertical steps and an offset-class LP transfer extend the rank-two excursion second moment of F_2 x Z with v = 2 down to multiplicity 15
distinct_from:
  fpbs-tree-projected-rank-two-excursion-second-moment: that uses no vertical edges and a lumped 2 x 2 same-vertex/same-fibre matrix, and settles v = 2 only for m >= 18; this adds one oriented vertical step per slot, splits the offset into the classes h = -c, 0, c and generic, and bounds the transfer by a monotone LP map, which settles v = 2 for m = 15, 16, 17 as well.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rigid decoration of every rank; this settles one more strip of rank-two multiplicities, for all heights, and records that the heights-uniform method does not reach m <= 14.
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the single example S_rig (m = 3) by pattern-specific certificates; this is uniform over heights and far from m = 3.
artifacts:
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/engine.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/certify_v.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/blockcheck_v.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/run.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/fm_scan.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/output.txt
---

**ESTABLISHED (2026-09-18, computer-assisted, unreviewed)** through
`fpbs-tree-projected-vertical-slot-second-moment-proof`.

**Statement.** Let `Gamma = F_2 x Z` with free basis `{a, b}`. Let `S` be a finite
symmetric generating set with `pi(S) ⊆ {1, a^±1, b^±1}`, `|D_a| = |D_b| = m`, and
vertical part `{(1, c), (1, -c)}` for some `c != 0` (so `v = 2`). The heights in
`D_a`, `D_b` and `c` are arbitrary. If `m in {15, 16, 17}`, then

```text
p_c(Cay(Gamma,S))  <=  p_m  <  p*(m,2)  <=  p_{2->2}  <=  p_u ,
```

with `p_15 = 2367/125000`, `p_16 = 1777/100000`, `p_17 = 837/50000`. Here `p*` is the
Ihara root of `fpbs-tree-projected-oriented-second-moment-thresholds`. So `p_c < p_u`.

Together with `fpbs-tree-projected-rank-two-excursion-second-moment` (`v = 2`,
`m >= 18`), rank two with `v = 2` and uniform multiplicity is settled for every
`m >= 15`, whatever the heights.

**Mechanism.**
1. *Ensemble.* This is the excursion trail of the earlier claim, with an optional
   vertical step `z -> z + c` in each slot, before the excursion. The step has a fixed
   orientation, so two vertical edges of one fibre are equal only when they start at
   the same height.
2. *Offset classes.* The offset `h` between two trails in a common fibre is recorded
   as `h = -c`, `0`, `c` or generic. That is 4 states instead of 2, and the class
   equations `h = k c` enter the linear systems symbolically. So every bound is
   still uniform over the heights.
3. *LP capacity map.* Adding a separate `h != 0` target double counts about `2/m` of
   the mass, which the class split cannot afford. Instead, each state gets a bound
   for each class and one capacity bound for the total mass into nonzero offsets. The
   pair sum over `k` prefix blocks is then bounded by `Phi^k(1)`, where `Phi` is the
   monotone homogeneous LP map "fill the nonzero classes greedily by descending
   weight, up to the capacity". The criterion is an exact Collatz-Wielandt vector
   with `Phi(y) < 3 w^2 y`.
4. *Calibration.* With vertical steps switched off, the LP map reproduces the
   thresholds of the lumped 2 x 2 matrix. `blockcheck_v.py` checks every symbolic
   bound against brute-force block sums on 8 concrete decorations, including `S_rig`
   and arithmetic progressions. The largest ratio of exact sum to bound is 0.963.

**Where it stops (recorded negative results).**
* *m <= 14.* The float bisection (`run.py`) gives the minimal passing `m p` shown
  below. The certificate fails at `m = 14`, with margin `-0.0045`.

  | m | 3 | 8 | 10 | 12 | 14 | 15 |
  |---|---|---|---|---|---|---|
  | needed `m p` | 0.382 | 0.296 | 0.291 | 0.287 | 0.2848 | 0.2839 |
  | `m p*` | 0.267 | 0.280 | 0.282 | 0.283 | 0.2837 | 0.2841 |
* *Deeper excursions make it worse.* Two excursions per slot (`J = 2`, 4512 symbolic
  terms) raise the first moment by 2-4%, but the heights-uniform counting bound loses
  more. The needed `m p` is 0.2996 at `m = 10` and 0.2849 at `m = 15`, both above the
  `J = 1` values, and `J = 2` passes only from `m = 16`. The loss is in the counting
  bound `m^comps (m-1)^fedges`, not in the ensemble.
* *First moment at small m.* `fm_scan.py` evaluates an upper bound for `3w` at `p*`.
  It is `0.9829` for `J = 1`, `0.9969` for `J = 2` and `0.9987` for `J = 3`, all at
  `m = 3` with one vertical step. So `E Z_N -> 0` at every `p <= p*(3,2)`, and no
  second moment over these ensembles reaches any `m = 3`, `v = 2` decoration. At
  `m = 4` the margin is below `3%` (`3w <= 1.0284`), far less than the pair
  correction.

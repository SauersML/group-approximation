---
rg: 2
id: hadamard-gadget-ratio-is-monotone-in-k
kind: claim
title: The best Had_k -> Max-2Lin(2) deletion ratio is non-decreasing in k, R*(k) <= R*(k+1), so L = lim R*(k) = sup R*(k) exists in [1.45685, 5/2] and a padding-line crossing exists iff L > 2
distinct_from:
  hadamard-gadget-deletion-ratio-window: that bounds each R*(k) separately (R*(k) < 2 for k <= 5, R*(k) <= 5/2 - 2^(1-k)); this compares consecutive levels, R*(k) <= R*(k+1), by lifting adversaries downward along a diagonal restriction.
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2 for some k; this reduces it to the single limit L = sup_k R*(k) and shows any witness propagates to every larger k.
  hadamard-crossing-needs-folding-gap: that bounds R*(k) by the relaxed value plus a folding gap at one fixed k; this relates true values across different k and says nothing about the relaxation.
artifacts:
  - experiments/ugc-hadamard-limit-2026-09-17/check_monotone_lift.py
---

**ESTABLISHED** (route `hadamard-gadget-ratio-is-monotone-in-k-proof`).

Notation is that of `hadamard-gadget-deletion-ratio-window`. `K = 2^k`, the
cube is `Q_k = {-1,1}^(F_2^k)`, the pins are `P_k = {+-chi_a : a in F_2^k}`,
and `z*(P_k)` is the minimum, over folded distributions on `Q_k` that are
random on `P_k`, of the maximum cut probability of a length-one edge.
`R*(k) = K z*(P_k)`.

**Statement.** For every `k >= 1`, `R*(k) <= R*(k+1)`. The same inequality
holds for the punctured pin set `P'_k` (characters with `a != 0`).

**Consequences.**

1. `L = lim_k R*(k) = sup_k R*(k)` exists, and
   `1.45685 <= L <= 5/2`. The lower end is `hadamard-gadget-ratio-k4-sandwich`;
   the upper end is item 2 of `hadamard-gadget-deletion-ratio-window`.
2. `hadamard-gadget-crosses-padding-line` holds iff `L > 2`. A witness
   `R*(k0) > 2` gives `R*(k) > 2` for every `k >= k0`.
3. Lower bounds propagate up: `R*(k) >= 11/8` for `k >= 3` and
   `R*(k) >= 331440289/227504128 ~ 1.45685` for every `k >= 4`.
4. Upper bounds propagate down: any certificate `R*(k1) <= 2` also certifies
   `R*(k) <= 2` for all `k <= k1`. A kill at one large `k` kills all smaller
   ones. For example, `hadamard-gadget-ratio-is-below-two-at-k6` gives
   `R*(6) < 2` and hence `R*(k) < 2` for every `k <= 6`.
5. If the Hadamard-gadget family fails to cross, it fails in the limit only.
   Killing it amounts to proving `L <= 2`. No finite-`k` kill is enough.

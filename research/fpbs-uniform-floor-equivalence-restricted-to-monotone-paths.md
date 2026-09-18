---
rg: 2
id: fpbs-uniform-floor-equivalence-restricted-to-monotone-paths
kind: claim
title: The floor-endpoint equivalence of the weighted-surface continuity claim holds in its repaired form, and the Z^2 anchors {a,t} and {b,t} fail at p >= 1/5
distinct_from:
  fpbs-weighted-surface-continuity-reduces-to-uniform-floor: that states the floor-endpoint equivalence for every path, which referees refuted; this is the repaired statement its proof route now needs, restricted to paths below the endpoint or put existentially, with the missing Z^2 anchors added.
  fpbs-one-edge-sprinkling-l2-lipschitz: that proves the sprinkling inequality and openness along any path; this asks only for the converse direction on monotone paths and for two explicit anchor computations.
  fpbs-l2-gap-class-closed-under-local-limits: that passes a uniform norm bound to local limits; this concerns one group along generator weights, and it is the referee gap in one proof route.
---

**OPEN.** This is the gap the referees found on 2026-09-17 in the route
`fpbs-weighted-surface-continuity-reduces-to-uniform-floor-proof`. They checked
the tree Schur test, the thresholds `p*_k` and the failures of the empty, `{t}`
and `{a}` anchors, and all of these hold. Two items are missing.

**Claim.** Let `Gamma` be finitely generated, `U` finite symmetric, and
`phi(q) = 1/||T_q||_{2->2}`.

1. **Repaired equivalence.** Let `gamma : [0,1] -> [0,1-eps]^U` be continuous,
   with `gamma(0)` good and `gamma(t) <= gamma(1) = p_c(S) 1_S` coordinatewise.
   Then critical l2 at `gamma(1)` is equivalent to `inf_t phi(gamma(t)) > 0`.
   Also, critical l2 at `gamma(1)` holds iff some path with that endpoint has a
   positive floor. So the floor is never a strictly weaker prerequisite.
   * The "every path" form is false. On `F_4 x Z`, a path through a
     supercritical point has `inf phi = 0`, but the `k = 4` tree anchor still
     certifies critical l2 at the endpoint.
2. **Z^2 anchors.** On `F_2 x Z = <a,b> x <t>`, the anchors `{a,t}` and `{b,t}`
   fail the one-step certificate at every `p >= 1/5`.
   * `output.txt` marks `{a,t}` inconclusive.
   * One referee's oriented-percolation lower bound (monotone paths over
     antidiagonals up to length 10) gives `chi_{Z^2}(1/5) >= 2.647`, so
     `2p chi > 1`. This bound is not yet in the repository.

Once both items are proved in the route file, drop this requirement from
`fpbs-weighted-surface-continuity-reduces-to-uniform-floor-proof`.

## Attempts

1. **Monotonicity along paths below the endpoint.** If `gamma(t) <= gamma(1)`
   coordinatewise, then `T_{gamma(t)} <= T_{gamma(1)}` entrywise, so
   `phi(gamma(t)) >= phi(gamma(1))`, which gives the converse. **Where it
   stops:** this has not yet been written into the route file, and the route's
   own sketch uses paths along the critical surface, which are not monotone.
2. **Z^2 anchors by an oriented-percolation lower bound.** Counting monotone
   open paths over antidiagonals up to length 10 gives
   `chi_{Z^2}(1/5) >= 2.647` (referee scratch computation). **Where it stops:**
   no script or output for this bound is in the repository, and the `{b,t}`
   case is only asserted by symmetry.

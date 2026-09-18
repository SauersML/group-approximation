---
rg: 2
id: ugc-via-parity-leaking-branch-selector
kind: route
title: A global parity-leaking branch selector with near-perfect YES lift value on Grassmann 2-to-1 instances is itself a unique-games hardness reduction
target: unique-games-conjecture
requires: [parity-leaking-branch-selectors-reach-near-perfect-completeness]
---

This route is the heretic decomposition of the UGC hole through computed
orientations.

1. **Reduction.** Compose the gap-3LIN reduction to `D(I)` with the polynomial-time
   selector `S`, and output the orientation lift `U_(S(I))`. This is a unique
   game. Its label set is `(L')^*` on each B-vertex, of size `2^(l-1)`, and the
   A-labels are the two extensions of a B-label along the branch vector `x_e`.
2. **Completeness.** On YES inputs, `val(U_(S(I))) >= 1 - eta'` by the
   prerequisite.
3. **Soundness.** Every lifted constraint `sigma|L' = tau and sigma(x_e) = o_e(tau)`
   implies the source constraint `sigma|L' = tau`. So
   `val(U_o) <= val(D(I)) <= delta` on NO inputs, for every orientation `o`.
4. **Conclusion.** `Gap-UG[1 - eta', delta]` is NP-hard for the given parameters.
   Letting `eta, delta -> 0` gives UGC.

The failure points are independent:
- the selector may not exist (prerequisite H1);
- the parity leakage it provably needs (`view-local-branch-selectors-are-gauge-blind`)
  may force it to decide the source, which is falsifier (i) of H1;
- non-honest witnesses may be the only way to exceed one half
  (`view-local-selectors-beat-one-half-through-non-honest-witnesses`).

Step 3 is also why a successful instance of this route would witness
`unique-games-hard-on-non-sse-grassmann-constraint-graphs`.

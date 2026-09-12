---
rg: 2
id: fpbs-twisted-level-percolation-connected
kind: claim
title: Twisted level percolation of the fibre group of a closed fibered hyperbolic 3-manifold is connected at every density
distinct_from:
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is the fixed price statement for extensions by bounded-cost normal subgroups; this is a connectivity statement about one explicit random graph on the fibre group, which gives fixed price one for the fibered group through fpbs-twisted-level-graph-generates-cyclic-extension.
  fpbs-twisted-level-graph-generates-cyclic-extension: that is the established criterion and Bernoulli identification; this is the open connectivity input the criterion needs.
---

**OPEN.**
- **Setting:** `M` is a closed hyperbolic 3-manifold fibering over the circle, with fibre group `N = pi_1(S_g)`, `g >= 2`, and monodromy `phi in Aut(N)`. So `pi_1(M) = N semidirect_phi Z`, and by Thurston's theorem `phi` represents a pseudo-Anosov class. `S` is a finite symmetric generating set of `N`.
- **Claim:** for every `delta > 0`, the random graph `T_delta(N, S, phi)` of `fpbs-twisted-level-graph-generates-cyclic-extension` is almost surely connected. Recall its construction: pairs `(u, m) in N x Z` are open independently with probability `delta`, and every open pair gives the edges `{u, phi^-m(s) u}` for `s in S`.
- **Why it matters:** with that criterion and `fpbs-bernoulli-maximal-cost`, it gives fixed price one for `pi_1(M)`. With virtual fibering, through `fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels`, it gives fixed price one for every closed hyperbolic 3-manifold group.

## Attempts

- **Truncating the levels is subcritical.** Keep only `|m| <= M`. The expected degree is at most `(2M+1)|S| delta`, and for small values each level is a subcritical star percolation, so every cluster is finite. Connectivity needs unboundedly many levels, i.e. arbitrarily long excursions of `t`. This rules out every bounded-range argument.
- **The count of infinite clusters.** `T_delta` is an `N`-invariant, insertion-tolerant percolation (open one pair). Every vertex has infinite degree almost surely, so there are no finite clusters. So `T_delta` is connected iff there is exactly one infinite cluster. The number of infinite clusters of an invariant, insertion-tolerant percolation is `1` or `infinity`. **Where it dies:** `N` is nonamenable, so Burton–Keane uniqueness is unavailable. Ruling out infinitely many clusters needs a mechanism that merges clusters along the long edges `phi^-m(s)` at exponentially separated scales. None is written.
- **Not automatic.** Item (5) of `fpbs-twisted-level-graph-generates-cyclic-extension` shows the analogous graph for `F_2 = F_infinity semidirect Z` is disconnected. A proof must use finite generation of `N`, i.e. the relations among `phi^-m(s)` (the surface relator, or the finite cost `2g-1` of `N`), not only that each vertex has infinitely many levels.
- **Finite quotients give no evidence.** Images of `T_delta` in finite quotients have growing average degree and connect for trivial reasons, while infinite nonamenable clusters can be infinite in number. No numerics were run.

---
rg: 2
id: fpbs-twisted-level-percolation-disconnected-at-low-density
kind: claim
title: Independent twisted level percolation on a torsion-free hyperbolic cyclic extension is almost surely disconnected at small density
invalidates:
  - fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels
distinct_from:
  fpbs-twisted-level-percolation-connected: that asserts almost sure connectivity at every density for closed fibered hyperbolic 3-manifolds; this proves the opposite at every small density, for every torsion-free hyperbolic N semidirect Z.
  fpbs-twisted-level-graph-generates-cyclic-extension: that is the generation criterion and the Bernoulli identification of the return graph; this is a disconnection theorem for that graph, so the criterion's item (3) never applies to independent levels on hyperbolic extensions.
---

**ESTABLISHED** through `fpbs-twisted-level-percolation-disconnected-proof`.

**Setting.**
- `Gamma = N semidirect_phi Z` is torsion-free and word-hyperbolic, and `N != 1`.
  The case `N = 1` is excluded: there `Gamma = Z`, `S` is empty and `T_delta` is one vertex, which is connected (review-swarm6-groups-2026-09-12 §3).
- `t` generates the `Z` factor, with `t u t^-1 = phi(u)`.
- `S` is a finite symmetric subset of `N \ {e}`.
- `T_delta(N, S, phi)` is the random graph of `fpbs-twisted-level-graph-generates-cyclic-extension`: pairs `(u, m) in N x Z` are open independently with probability `delta`, and an open pair gives the edges `{u, phi^-m(x) u}` for `x in S`.

**Claim.** There is `delta_0 = delta_0(Gamma, t, S) > 0` such that for every `delta in (0, delta_0)`:
1. `P(e and s in the same cluster) < 1` for every `s in S`;
2. `T_delta(N, S, phi)` is almost surely disconnected.

**Consequences.**
- The 3-manifold case: let `M` be a closed hyperbolic 3-manifold fibering over the circle, with fibre group `N` and a finite symmetric generating set `S`. Then `pi_1(M)` is a torsion-free cocompact Kleinian group, so it is hyperbolic. So `fpbs-twisted-level-percolation-connected` is false.
- The route `fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels` is invalidated, because it needs connectivity for arbitrarily small `delta`.
- By item (1) of `fpbs-twisted-level-graph-generates-cyclic-extension`, the transport graphing `{t} ∪ {s|_A}` with `A = {x(e) < delta}` does not generate the Bernoulli orbit relation of `pi_1(M)` for small `delta`.

**Not settled.**
- Fixed price itself: `fpbs-hyperbolic-3-manifold-groups-fixed-price-one` stays OPEN.
- Transport graphings built from other Borel sets `A`. The path count in the proof is combinatorial, and only the probability step uses independence. `fpbs-line-independent-twisted-levels-disconnected` extends the result, with the same `delta_0`, to open levels correlated arbitrarily along `t`-orbits but independent across fibre lines. Sets that correlate openness across fibre lines are not ruled out; see `fpbs-cross-line-correlated-transport-set-generates`.

**Consistency with main.**
- In item (4) of the criterion (`phi = id`, connected), `t` is central, so `<t>` is not malnormal and the hypothesis fails.
- Item (5) (`F_2`, disconnected) is an instance of this claim.

No novelty or priority is claimed.

---
rg: 2
id: fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels
kind: route
title: Pass to a fibered cover, generate its Bernoulli orbit relation by the transport graphing through twisted level percolation, and transfer back through finite index
target: fpbs-hyperbolic-3-manifold-groups-fixed-price-one
requires:
  - fpbs-twisted-level-graph-generates-cyclic-extension
  - fpbs-twisted-level-percolation-connected
  - fpbs-bernoulli-maximal-cost
  - fpbs-fibered-3-manifold-cost-inputs
---

Written derivation.

1. **Fibered cover.** Let `M` be a closed hyperbolic 3-manifold. By virtual fibering (`fpbs-fibered-3-manifold-cost-inputs`, item 1), a finite cover `M'` fibers over the circle. So `Gamma' = pi_1(M') = N semidirect_phi Z` has finite index in `Gamma = pi_1(M)`, with `N` a closed surface group. `M'` is a closed hyperbolic 3-manifold that fibers.
2. **The Bernoulli shift has cost one.** Take a finite symmetric generating set `S` of `N`. By `fpbs-twisted-level-percolation-connected`, `T_delta(N, S, phi)` is almost surely connected for every `delta > 0`. Item (3) of `fpbs-twisted-level-graph-generates-cyclic-extension` then gives `C(b_(Gamma')) = 1`.
3. **Fixed price for the cover.** `Gamma'` is finitely generated, so every free p.m.p. action of `Gamma'` has cost at most `C(b_(Gamma'))`, by `fpbs-bernoulli-maximal-cost`. Every such action also has cost at least `1`. So `Gamma'` has fixed price one.
4. **Transfer to `Gamma`.** A finite-index subgroup is commensurated. By item 3 of `fpbs-fibered-3-manifold-cost-inputs`, `C(R_(Gamma↷X)) <= C(R_(Gamma'↷X)) = 1` for every free p.m.p. action of `Gamma`, so `Gamma` has fixed price one.

This route is dependency bookkeeping for a written deduction, not a formal verification. It stays open while `fpbs-twisted-level-percolation-connected` is open.

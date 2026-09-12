---
rg: 2
id: fpbs-hyperbolic-3-manifold-fixed-price-via-normal-subgroup
kind: route
title: Pass to a fibered cover, apply the bounded-cost normal subgroup statement to the fiber group, and transfer back through finite index
target: fpbs-hyperbolic-3-manifold-groups-fixed-price-one
requires:
  - fpbs-normal-subgroup-bounded-cost-fixed-price-one
  - fpbs-fibered-3-manifold-cost-inputs
---

Written derivation.
1. Let `M` be a closed hyperbolic 3-manifold. By virtual fibering, a finite
   cover `M'` fibers over the circle with a closed fiber `S` of genus `g >= 2`.
   So `Gamma' = pi_1(M') = pi_1(S) semidirect Z`, of finite index in
   `Gamma = pi_1(M)`.
2. `N = pi_1(S)` is an infinite normal subgroup of `Gamma'`, and `Gamma'/N` is
   infinite cyclic. Surface groups have fixed price, so every free p.m.p.
   action of `N` has cost `2g-1 =: K`.
3. `fpbs-normal-subgroup-bounded-cost-fixed-price-one` then gives `Gamma'`
   fixed price one.
4. A finite-index subgroup is commensurated. Gaboriau's Corollary 2.49 gives
   `C(R_(Gamma↷X)) <= C(R_(Gamma'↷X)) = 1` for every free p.m.p. action of
   `Gamma`, since its restriction to `Gamma'` is free. Every aperiodic relation
   has cost at least one, so `Gamma` has fixed price one.

The three inputs are imported in `fpbs-fibered-3-manifold-cost-inputs`. This
is dependency bookkeeping for a written deduction, not a formal verification.

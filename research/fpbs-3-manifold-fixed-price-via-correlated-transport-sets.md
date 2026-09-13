---
rg: 2
id: fpbs-3-manifold-fixed-price-via-correlated-transport-sets
kind: route
title: Pass to a fibered cover, generate its Bernoulli orbit relation by a small correlated transport set, and transfer back through finite index
target: fpbs-hyperbolic-3-manifold-groups-fixed-price-one
requires:
  - fpbs-twisted-level-graph-generates-cyclic-extension
  - fpbs-cross-line-correlated-transport-set-generates
  - fpbs-bernoulli-maximal-cost
  - fpbs-fibered-3-manifold-cost-inputs
artifacts:
  - research/artifacts/fpbs/docs/twisted-levels-line-independent-disconnection.md
---

Written derivation. This is the same bookkeeping as the invalidated route `fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels`, with its refuted premise replaced by the open claim `fpbs-cross-line-correlated-transport-set-generates`.

1. **Fibered cover.** By virtual fibering (`fpbs-fibered-3-manifold-cost-inputs`, item 1), a closed hyperbolic 3-manifold `M` has a finite cover `M'` fibering over the circle, with `Gamma' = pi_1(M') = N semidirect_phi Z`.
2. **The Bernoulli shift has cost one.** `fpbs-cross-line-correlated-transport-set-generates` gives, for every `epsilon > 0`, a Borel `A` with `mu(A) < epsilon` whose transport graphing generates. That graphing costs at most `1 + |S| epsilon`, so `C(b_(Gamma')) = 1`.
3. **Fixed price for the cover.** Every free p.m.p. action of `Gamma'` has cost at most `C(b_(Gamma'))` (`fpbs-bernoulli-maximal-cost`) and at least `1`.
4. **Transfer.** By item 3 of `fpbs-fibered-3-manifold-cost-inputs`, fixed price one passes from `Gamma'` to `pi_1(M)`.

The route fires only if the open premise is proved. This is dependency bookkeeping, not a formal verification.

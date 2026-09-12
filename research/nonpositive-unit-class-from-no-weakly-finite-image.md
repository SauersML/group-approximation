---
rg: 2
id: nonpositive-unit-class-from-no-weakly-finite-image
kind: route
title: With no weakly finite image the summand fails the rank condition, so no state exists and the unit class is nonpositive
target: ternary-anti-central-unit-class-is-nonpositive
requires: [ternary-anti-central-summand-has-no-weakly-finite-image, rank-condition-rings-have-weakly-finite-images, anti-central-state-obstruction-equals-stable-finiteness]
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Corollary C.2.
1. By the first requirement, `S_-` has no nonzero weakly finite image.
2. By `rank-condition-rings-have-weakly-finite-images`, `S_-` fails the rank condition.
3. So `(K_0(S_-), [eps_-])` has no state, and part 2 of `anti-central-state-obstruction-equals-stable-finiteness`
   gives `k[eps_-] <= 0` for some `k >= 1`, which is the target.

The first requirement is also necessary for the target: the rank condition fails in `S_-` and hence in
every image. So the route loses nothing, and it needs neither (U1) nor (U2).

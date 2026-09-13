---
rg: 2
id: actor-liftable-masa-from-one-level-hs-kun-decomposition
kind: route
title: The universal one-level HS Kun decomposition, applied to the Kun--Thom actor, lifts a masa of every model's actor commutant
target: actor-commutant-has-liftable-masa-in-every-model
requires: [hs-one-level-expander-block-decomposition, liftable-masa-in-every-model-iff-uniform-hs-kun-partitions]
artifacts:
  - research/artifacts/hs-masa-lift-positive-2026-09-13.md
---

1. `hs-one-level-expander-block-decomposition` is stated for every finitely generated Kazhdan group.
   Apply it to the actor `G = <Gamma, A, B>`, which is Kazhdan.
2. Item (iv) of Theorem 2 in the artifact (the one-level clause of
   `liftable-masa-in-every-model-iff-uniform-hs-kun-partitions`) then gives a liftable masa of
   `sigma(G)' cap prod_U M_n` for every model `sigma`. The removed corner is adjoined as one more
   block, at boundary cost `2 tau(q_0)` and slack cost `kappa'^2 tau(q_0)`.
3. In particular this holds for every model satisfying (H1), which is the target.

The route fires only if the universal one-level decomposition is proved. That statement is strictly
stronger than what the target needs: it asks for the per-block gap, which spiky vectors violate,
while the target needs only the bounded summed form `DEC_kappa`.

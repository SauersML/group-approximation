---
rg: 2
id: sl3z-incoherent-via-rfrs-cd2-positive-b2
kind: route
title: A two-dimensional virtually RFRS subgroup with positive second L2-Betti number makes SL_3(Z) incoherent
target: sl3z-is-incoherent
requires:
  - sl3z-contains-rfrs-cd2-subgroup-with-positive-b2
  - virtually-rfrs-cd2-coherence-characterization
---

Let `G <= SL_3(Z)` be finitely generated, virtually RFRS, with
`cd_Q(G) <= 2` and `b_2^(2)(G) > 0`. Take `k = Q` in
`virtually-rfrs-cd2-coherence-characterization`. There, item 1 (`G` is
coherent) is equivalent to item 6 (`b_2^(2)(G) = 0`). Item 6 fails, so `G` is
not coherent: some finitely generated subgroup of `G` is not finitely
presented. That subgroup is a subgroup of `SL_3(Z)`.

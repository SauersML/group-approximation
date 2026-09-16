---
rg: 2
id: automatic-groups-are-of-type-f-infinity
kind: claim
title: Every automatic group is of type F_infinity, and hence of type FP_infinity
distinct_from:
  torsion-free-automatic-groups-have-finite-cd: that open claim bounds the cohomological dimension of torsion-free automatic groups; this is the established finiteness of skeleta, which says nothing about dimension
  automatic-groups-have-contractible-rips-complexes: that open claim asks for a contractible Rips complex at a single scale; this is the weaker coarse statement that skeleta can be made finite, established by import
---

Let `G` be automatic (ECHLPT, *Word Processing in Groups*, 1992). Then `G` is of type
`F_∞`: for every `n`, `G` has a `K(G, 1)` with finite `n`-skeleton. Consequently `G` is
of type `FP_∞`. For each `n`, the cellular chain complex of the universal cover of such a
`K(G, 1)` is a free resolution of `Z` over `ZG` that is finitely generated in degrees
`<= n`, so `G` is of type `FP_n` for all `n`.

This is Alonso's theorem that groups with bounded combings are of type `FP_∞` (Alonso,
*Combings of groups*, 1992) together with finite presentability, as cited by Zaremsky,
Brittenham–Hermiller–Johnson and Engel–Wulff. Citation route:
`automatic-groups-are-of-type-f-infinity-citation`.

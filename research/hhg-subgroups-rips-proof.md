---
rg: 2
id: hhg-subgroups-rips-proof
kind: route
title: Finite-index subgroups inherit a proper cobounded action on the coarsely injective space
target: torsion-free-hhg-subgroups-have-contractible-rips-complexes
requires:
  - hierarchically-hyperbolic-groups-are-coarsely-injective
  - coarsely-injective-groups-have-contractible-rips-complexes
---

By the first required claim, `H` acts properly and cocompactly by isometries on a
coarsely injective space `(X, σ)`; so every point is within some `D_H` of `H x_0`. The
restricted action of `G` is still proper.

It is cobounded. Write `H = G h_1 ∪ … ∪ G h_k`. A point within `D_H` of `g h_i x_0` is
within `D_H + σ(h_i x_0, x_0)` of `g x_0`, so every point is within
`D = D_H + max_i σ(h_i x_0, x_0)` of `G x_0`.

`G` is torsion-free, so the second required claim applies. ∎

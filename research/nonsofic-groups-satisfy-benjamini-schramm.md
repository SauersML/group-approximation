---
rg: 2
id: nonsofic-groups-satisfy-benjamini-schramm
kind: claim
title: Every finitely generated nonsofic group has p_c < p_u on every Cayley graph
distinct_from:
  fpbs-benjamini-schramm-universal: that is the Benjamini--Schramm conjecture for every nonamenable group; this is its restriction to nonsofic groups, where the soficity threshold of cluster relations gives an extra route and the cost and Betti routes are often empty.
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

**OPEN.** Let `G` be a finitely generated nonsofic group and `S` a finite symmetric generating set. Then
Bernoulli bond percolation on `Cay(G,S)` has `p_c < p_u`.

Nonsofic groups are nonamenable, so this is the Benjamini--Schramm conjecture restricted to nonsofic groups.

**Why it is a separate node.** The known nonsofic groups have fixed price one and vanishing first
`L^2`-Betti number (`leavitt-unit-groups-have-fixed-price-one`,
`fpbs-elementary-matrix-semidirect-fixed-price-one`). So the cost route
(`fpbs-non-fixed-price-one-has-nonuniqueness`) and the Betti route do not reach them. The soficity threshold
gives a route of a different kind: `p_c <= p_sof <= p_u`, so one sofic supercritical cluster relation is
enough (`nonsofic-benjamini-schramm-from-sofic-supercritical-clusters`).

## Attempts

- **Cost and Betti numbers.** Empty for the binary Leavitt unit group and for the Kun--Thom groups, which
  have fixed price one.
- **Soficity threshold.** Reduced to `some-supercritical-cluster-relation-is-sofic`, which is open.

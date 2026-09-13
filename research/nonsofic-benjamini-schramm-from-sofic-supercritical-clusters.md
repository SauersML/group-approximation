---
rg: 2
id: nonsofic-benjamini-schramm-from-sofic-supercritical-clusters
kind: route
title: A sofic supercritical cluster relation lies below the soficity threshold, which lies below p_u
target: nonsofic-groups-satisfy-benjamini-schramm
requires:
  - nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu
  - some-supercritical-cluster-relation-is-sofic
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

Let `G` be nonsofic and `S` a finite symmetric generating set.

1. By `some-supercritical-cluster-relation-is-sofic` there is `p > p_c` with `R_p` sofic.
2. By `nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu`, part 2, no `p > p_u` has `R_p` sofic.
   So `p <= p_u`.
3. Hence `p_c < p <= p_u` (artifact, Corollary 3.2).

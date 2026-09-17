---
rg: 2
id: cluster-entropy-certificates-fail-on-kazhdan-groups-proof
kind: route
title: Kazhdan groups are one-ended by Watatani and Stallings, then apply the fat-digon obstruction
target: cluster-entropy-certificates-fail-on-kazhdan-groups
requires:
  - property-t-implies-property-fa
  - several-ended-groups-act-fixed-point-freely-on-trees
  - cluster-entropy-functionals-vanish-on-one-ended-bernoulli
artifacts:
  - research/artifacts/cluster-entropy-functionals-one-ended-obstruction-2026-09-17.md
---

Corollary 3.4 of the artifact.

1. A group with property (T) is finitely generated. This is part of the statement recorded on
   `property-t-implies-property-fa`.
2. An infinite finitely generated group has `e(G) >= 1`: removing a finite set from its infinite,
   connected, locally finite Cayley graph leaves at least one infinite component.
3. If `e(G) > 1`, then `G` acts on a tree without a global fixed point
   (`several-ended-groups-act-fixed-point-freely-on-trees`). This contradicts FA
   (`property-t-implies-property-fa`). So `G` is one-ended.
4. Apply `cluster-entropy-functionals-vanish-on-one-ended-bernoulli`.

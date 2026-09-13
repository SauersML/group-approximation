---
rg: 2
id: some-hyperbolic-group-in-no-nv-via-kazhdan-finiteness
kind: route
title: If Kazhdan subgroups of every nV are finite, an infinite hyperbolic Kazhdan group embeds in no nV
target: some-hyperbolic-group-embeds-in-no-brin-thompson-group
requires:
  - kazhdan-subgroups-of-brin-thompson-groups-are-finite
  - torsion-free-hyperbolic-kazhdan-partner-exists
---

1. By `torsion-free-hyperbolic-kazhdan-partner-exists` there is an infinite,
   non-elementary, finitely presented, word-hyperbolic group `H` with property
   (T).
2. Suppose `φ: H → nV` is injective for some n. Then `φ(H) ≅ H` is an infinite
   subgroup of nV with property (T). That contradicts
   `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.
3. So `H` embeds in no nV. This is the negative answer to Zaremsky Problem
   2.19(a).

The route is a genuine reduction, not a restatement. The negative answer could
also come from an obstruction that says nothing about Kazhdan subgroups, and the
required claim is strictly stronger in scope.

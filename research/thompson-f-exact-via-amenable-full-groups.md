---
rg: 2
id: thompson-f-exact-via-amenable-full-groups
kind: route
title: F is a subgroup of V, the topological full group of the amenable Cuntz groupoid
target: thompson-group-f-is-exact
requires:
  - amenable-groupoid-full-groups-are-exact
  - exact-groups-are-closed-under-extensions
---

1. The Cuntz groupoid `𝒢_2` of the full one-sided 2-shift (the groupoid of `O_2`) is an amenable ample
   Hausdorff groupoid with Cantor unit space. Its topological full group is Thompson's `V`. Both facts are
   standard (Renault; Matui and Nekrashevych) and are recalled, not re-read.
2. By `amenable-groupoid-full-groups-are-exact`, `V` is exact.
3. `F ≤ V`, and exactness passes to subgroups (`exact-groups-are-closed-under-extensions`). ∎

---
rg: 2
id: kazhdan-nv-finite-via-measured-minimal-sets
kind: route
title: If minimal sets of Kazhdan subgroups of nV carry invariant measures, the measure criterion makes those subgroups finite
target: kazhdan-subgroups-of-brin-thompson-groups-are-finite
requires:
  - kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures
  - minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures
artifacts:
  - research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md
---

1. Let `K <= nV` have property (T).
2. By `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`, every
   minimal closed `K`-invariant subset of `C^n` carries a `K`-invariant probability
   measure.
3. By `kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures` (part 2, the
   fourth condition implies the first), `K` is finite.

The first prerequisite is established; the second is open and is equivalent to the
target. The route isolates what remains: a measure-existence statement for Kazhdan
subgroups acting on the cube, rather than a proper action, a commensurated set, or the
Haagerup property of nV.

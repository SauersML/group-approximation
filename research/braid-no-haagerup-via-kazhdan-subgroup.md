---
rg: 2
id: braid-no-haagerup-via-kazhdan-subgroup
kind: route
title: "Dead: an infinite Kazhdan subgroup of a braid group would kill the Haagerup property"
target: some-braid-group-lacks-the-haagerup-property
requires:
  - braid-group-contains-infinite-kazhdan-subgroup
---

Dead. Its prerequisite is refuted (`braid-groups-have-no-nontrivial-kazhdan-subgroups`, which also invalidates
this route).

The implication itself is sound. If `H ≤ B_n` is infinite with property (T), every affine isometric action of
`H` on a Hilbert space has a fixed point (Delorme–Guichardet), so every conditionally negative definite
function on `B_n` is bounded on `H`, and none is proper.

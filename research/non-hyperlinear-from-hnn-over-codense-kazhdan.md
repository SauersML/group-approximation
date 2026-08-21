---
rg: 2
id: non-hyperlinear-from-hnn-over-codense-kazhdan
kind: route
title: Centralize the co-dense Kazhdan subgroup of a stable host by a new letter
target: non-hyperlinear-group
requires:
  - stable-group-with-codense-kazhdan-subgroup
  - hnn-over-codense-kazhdan-subgroup-not-hyperlinear
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Given the host pair `(A, C)`, the HNN extension `<A, t | [t, C] = 1>` is a
finitely presented nonhyperlinear group by
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`; with
`(SL_2(Z[1/pq]), SL_2(Z[1/p]))` the one remaining input is the flexible
HS-stability of `SL_2(Z[1/pq])`.  This supersedes
`non-hyperlinear-from-pauli-lamplighter`, which needs the same inputs and
a more elaborate group.

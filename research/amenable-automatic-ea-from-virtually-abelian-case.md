---
rg: 2
id: amenable-automatic-ea-from-virtually-abelian-case
kind: route
title: Virtually abelian groups are abelian-by-finite, hence elementary amenable
target: amenable-automatic-groups-are-elementary-amenable
requires:
  - amenable-automatic-groups-are-virtually-abelian
---

## Why sufficient

Let `G` be amenable and automatic. By the prerequisite, `G` has an abelian subgroup `B` of
finite index. Its normal core `N = ⋂_{g ∈ G} gBg^{-1}` is an intersection of at most
`[G : B]` conjugates, each of finite index, so `N` is a normal abelian subgroup of finite
index. So `G` is an extension of the abelian group `N` by the finite group `G/N`. Chou's
class `EG` contains all abelian and all finite groups and is closed under extensions, so
`G ∈ EG`.

This is the second forward half of Proposition 6 in
`research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
Section 6.

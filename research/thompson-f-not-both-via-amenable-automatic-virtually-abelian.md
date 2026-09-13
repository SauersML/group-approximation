---
rg: 2
id: thompson-f-not-both-via-amenable-automatic-virtually-abelian
kind: route
title: If amenable automatic groups are virtually abelian then F is not both amenable and automatic
target: thompson-f-is-not-both-amenable-and-automatic
requires:
  - amenable-automatic-groups-are-virtually-abelian
---

`F` is not virtually abelian. It contains `Z^n` for every `n`: see step 3 of
`thompson-f-has-no-contractible-rips-complex-proof`, using nontrivial elements with
disjoint supports. A group with an abelian subgroup `A` of finite index is virtually
`Z^m` for `m` the torsion-free rank of `A`, and a free abelian subgroup `B` meets `A`
in a subgroup of finite index in `B`, so `rank B <= m`. Hence the free abelian
subgroups of a virtually abelian group have bounded rank, and `F` has none of
bounded rank.

So if `F` were amenable and automatic, the prerequisite would make `F` virtually
abelian, a contradiction.

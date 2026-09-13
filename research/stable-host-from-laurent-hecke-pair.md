---
rg: 2
id: stable-host-from-laurent-hecke-pair
kind: route
title: A flexibly stable SL_3(F_2[t,1/t]) is a stable host with the co-dense Kazhdan subgroup SL_3(F_2[t])
target: stable-group-with-codense-kazhdan-subgroup
requires:
  - sl3-laurent-f2-is-flexibly-hs-stable
  - function-field-hecke-pair-is-perfect-codense-kazhdan
---

Take `G=SL_3(F_2[t,1/t])` and `G_0=SL_3(F_2[t])`.  By item 1 of
`function-field-hecke-pair-is-perfect-codense-kazhdan`, both are finitely
generated and `G_0` is Kazhdan, hence (T;FD).  `G_0` has infinite index,
since `G/G_0` is the infinite set of type-zero building vertices.  Item 2
gives `pi^(G_0)=pi^G` for every finite-dimensional unitary representation.
The target claim says that flexible stability in the Dogon--Vigdorovich sense
suffices, and that is the first required claim.

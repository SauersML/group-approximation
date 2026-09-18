---
rg: 2
id: automatic-p-subgroup-ball-via-rips
kind: route
title: Contractible Rips complexes of automatic groups would conjugate their finite p-subgroups into a ball
target: automatic-groups-conjugate-finite-p-subgroups-into-a-ball
requires:
  - automatic-groups-have-contractible-rips-complexes
  - contractible-rips-conjugates-p-subgroups-into-balls
---

Let `G` be automatic. By `automatic-groups-have-contractible-rips-complexes` there
are `S` and `d` with `R_d(G,S)` contractible. By
`contractible-rips-conjugates-p-subgroups-into-balls`, item 2, every finite
`p`-subgroup `P` satisfies `y^-1 P y ⊆ B_S(d)` for some `y`. Hence
`|P| <= |B_S(d)|`, and there are at most `2^|B_S(d)|` conjugacy classes of finite
subgroups of prime-power order.

This is a genuine reduction, not a restatement. The target asks for a specific
contractible complex. This conclusion is a purely algebraic finiteness statement
about torsion, which is independent of the dimension statement
`torsion-free-automatic-groups-have-finite-cd`.

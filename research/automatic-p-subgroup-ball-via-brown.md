---
rg: 2
id: automatic-p-subgroup-ball-via-brown
kind: route
title: Virtual torsion-freeness plus finite cd of torsion-free automatic groups gives the p-subgroup ball through Brown's lemma
target: automatic-groups-conjugate-finite-p-subgroups-into-a-ball
requires:
  - automatic-groups-are-virtually-torsion-free
  - torsion-free-automatic-groups-have-finite-cd
  - automatic-finite-vcd-groups-have-few-p-subgroup-classes
  - finite-index-subgroups-of-automatic-groups-are-automatic
---

Let `G` be automatic. By `automatic-groups-are-virtually-torsion-free`, `G` has a torsion-free
subgroup `H_0` of finite index. By `finite-index-subgroups-of-automatic-groups-are-automatic`,
`H_0` is automatic. By `torsion-free-automatic-groups-have-finite-cd`, `cd_Z H_0 < ∞`. Then
`automatic-finite-vcd-groups-have-few-p-subgroup-classes` gives, for every prime `p`,
finitely many conjugacy classes of finite `p`-subgroups and a radius `R` with every finite
`p`-subgroup conjugate into `B_S(R)`. This is the target.

**Consequence for the wave-4 decomposition.** `automatic-p-subgroup-ball-via-rips` and the
2026-09-17 w4 attempt on `automatic-groups-have-contractible-rips-complexes` describe the torsion
condition as independent of the dimension condition. For virtually torsion-free automatic groups
that is not so: the dimension condition, applied to one torsion-free finite-index subgroup,
implies the torsion condition. So a torsion obstruction to contractible Rips complexes can be
genuinely new only in a non-VTF automatic group, and producing one would also require resolving
the non-VTF question for automatic groups.

The two prerequisites can fail independently. `automatic-groups-are-virtually-torsion-free`
contains the hyperbolic VTF root, and `torsion-free-automatic-groups-have-finite-cd` is a
dimension question about torsion-free groups.

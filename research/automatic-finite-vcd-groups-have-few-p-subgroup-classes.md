---
rg: 2
id: automatic-finite-vcd-groups-have-few-p-subgroup-classes
kind: claim
title: An automatic group with a torsion-free finite-index subgroup of finite cd has finitely many conjugacy classes of p-subgroups, all conjugate into one ball
distinct_from:
  automatic-groups-conjugate-finite-p-subgroups-into-a-ball: that open claim asks the torsion conclusion for every automatic group; this established claim proves it under finite virtual cohomological dimension, which localises every counterexample to the non-VTF or infinite-vcd case
  contractible-rips-conjugates-p-subgroups-into-balls: that claim gets the same conclusion from a contractible Rips complex via Smith theory; this one needs no Rips complex, only finite vcd and FP_infinity, via Brown's lemma
  brown-finite-p-subgroup-classes-from-finite-mod-p-cohomology: that is the imported algebraic lemma; this is its application to automatic groups, including the FP_infinity finiteness check and the passage from finitely many classes to a single ball
---

**ESTABLISHED** (route `automatic-groups-of-finite-vcd-p-subgroup-classes-proof`).

Let `G` be automatic, with finite generating set `S`. Suppose `G` has a torsion-free subgroup of
finite index whose cohomological dimension over `Z` is finite. Then for every prime `p`:

1. `G` has only finitely many conjugacy classes of finite `p`-subgroups;
2. there is a bound on the orders of finite `p`-subgroups of `G`;
3. there is `R` such that every finite `p`-subgroup of `G` is conjugate into `B_S(R)`.

**Contrapositive (localisation).** Suppose an automatic group `G` violates the torsion conclusion
of `automatic-groups-conjugate-finite-p-subgroups-into-a-ball` at some prime `p`. Then either
`G` is not virtually torsion-free, or every torsion-free finite-index subgroup of `G` is a
torsion-free automatic group of infinite cohomological dimension. In the second case that
subgroup is automatic by `finite-index-subgroups-of-automatic-groups-are-automatic`, so it is a
counterexample to `torsion-free-automatic-groups-have-finite-cd`.

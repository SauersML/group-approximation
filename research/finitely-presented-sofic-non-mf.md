---
rg: 2
id: finitely-presented-sofic-non-mf
kind: claim
title: A finitely presented sofic and hyperlinear group that is not MF
root: true
distinct_from:
  sofic-non-mf-witness: That established claim gives the FINITELY GENERATED Clifford witness `W`; this gives the finitely presented source `E` itself, which is a strictly stronger separation.
  literal-group-sofic: That claim is soficity of `E` alone; this packages soficity together with finite presentation and failure of MF as the separation statement.
  hyperlinear-not-imply-mf: That claim needs only some hyperlinear non-MF group and is served by the finitely generated witness; this one asserts the finitely presented, simultaneously sofic statement.
  literal-group-fails-mf-conventions: That records which MF conventions `E` fails; this adds the positive approximation side.
  literal-group-not-sofic: That claim (refuted) denies soficity of `E`; this one asserts it, together with finite presentation and failure of MF.
  hyperlinear-nonsofic-group: That root wants a hyperlinear group that is NOT sofic; this group is sofic, and the property it lacks is MF, not soficity.
  torsion-free-finitely-presented-non-mf: That asks for a torsion-free non-MF group; this group has a central involution, and the content added here is the positive approximation side.
  non-hyperlinear-group: That asks for a group failing hyperlinearity; this group is hyperlinear and fails only MF.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - non_mf_groups_exist.tex
---

The literal forty-one-relator group `E` is finitely presented, sofic, and
hyperlinear, and is not MF in any of the formalized operator-norm
matrix-corona conventions.

This strengthens Theorem E of the manuscript from the finitely generated
witness `W = ClLamp(X) semidirect V` to the finitely presented source, and it
separates the two approximation radicals on one finitely presented group:

    Rad_sof(E) = 1   while   {1,w} <= Rad_MF(E),  w != 1.

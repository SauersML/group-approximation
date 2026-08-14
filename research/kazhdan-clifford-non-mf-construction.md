---
rg: 2
id: kazhdan-clifford-non-mf-construction
kind: claim
title: Kazhdan--Clifford construction of finitely presented non-MF groups
distinct_from:
  scaling-family-non-mf: This is the abstract construction from an arbitrary proper Kazhdan self-embedding; the scaling claim is its concrete affine family.
  torsion-free-finitely-presented-non-mf: This construction produces a nontrivial central involution; the other asks for a torsion-free example beyond the present mechanism.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/KazhdanCliffordConstruction.lean
---

Every finitely presented property-(T) group with a proper injective
self-embedding yields, from any element outside the image, a finitely
presented group with a nontrivial central involution killed by every
norm-matrix-corona representation.  In particular the constructed group is
not MF.

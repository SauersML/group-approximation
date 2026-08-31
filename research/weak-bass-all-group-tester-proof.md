---
rg: 2
id: weak-bass-all-group-tester-proof
kind: route
title: Use identity-coefficient finite support at arbitrary colimits
target: weak-bass-fixed-two-generator-all-group-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - weak-bass-two-generator-tester-proof
---

Let `B_w` be the class of groups satisfying integral weak Bass.

The subgroup argument in [[weak-bass-two-generator-tester-proof]] has no
torsion hypothesis. If `H<=G`, the inclusion of group rings preserves the
identity coefficient of an idempotent-matrix trace, and augmentation is
natural for every group homomorphism. Hence weak Bass for `G` implies weak
Bass for `H`.

The colimit argument there also has no torsion hypothesis. For
`G=colim_i G_i`, lift the two finite idempotent matrices representing a
class in `K_0(Z[G])` to one stage and pass to a stage where their idempotent
equations hold. The difference of their ordinary traces has finite support.
Every supported element which becomes the identity in `G` does so at one
later stage; choose a common stage for the finite support. At that stage
both augmentation and the identity coefficient equal their final values.
Thus weak Bass at all stages implies weak Bass at the colimit, even when
the structure maps are noninjective.

Therefore `B_w` is subgroup-closed and closed under arbitrary directed
colimits. Applying
[[universal-all-group-subgroup-colimit-class-tester]] gives the claimed
fixed-host equivalence. QED

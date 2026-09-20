---
rg: 2
id: nonhyperlinear-bcc-group-via-native-rips-double
kind: route
title: "Use the same native Rips double for the nonhyperlinear and positive assembly conclusions"
target: fp-torsion-free-nonhyperlinear-bcc-group-exists
requires: ["leavitt-native-strict-kazhdan-compression-pair", "leavitt-unit-group-finitely-presented", "ollivier-wise-kazhdan-rips-construction", "kazhdan-compression-pairs-normalize-all-tracial-models", "rips-doubles-satisfy-bc-with-coefficients", "assembly-image-traces-are-integral-for-torsion-free-groups"]
artifacts:
  - research/artifacts/torsion-free-nonhyperlinear-rips-double-2026-09-20.md
---


Apply the artifact's construction to Q=EL_4(R)≅R^x and
Gamma=diag(EL_3(R),1). The first two prerequisites supply its strict
Kazhdan compression pair and finite presentation. Ollivier–Wise gives
a torsion-free hyperbolic G of cd_Z<=2 and two-generated Kazhdan
kernel. The preimage H is finitely generated and Kazhdan; G is
Kazhdan too. The finite compressors lift and generate G with H.

Choose t strict and h in H\tHt^-1. Every tracial matrix image of
P=G *_H G kills w=[h,t_2 t_1^-1], by normalization applied to
c=t_1^-1 t_2 in the H centralizer. Its reduced word
(ht)_2 (t^-1 h^-1 t)_1 (t^-1)_2 has all syllables outside H, so w!=1.
Two finite presentations for G and finitely many H identifications
present P. Tree stabilizers give torsion-freeness and the induced
resolution bound cd_Z P<=3. The Rips-double BCC prerequisite applies
to this very same P, not an unrelated existential witness.

Ordinary assembly and torsion-free trace integrality give trace range
ℤ. A nontrivial scalar projection would have faithful trace strictly
between 0 and 1, impossible. These trace consequences do not require
the normalization theorem.

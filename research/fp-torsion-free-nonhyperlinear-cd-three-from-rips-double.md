---
rg: 2
id: fp-torsion-free-nonhyperlinear-cd-three-from-rips-double
kind: route
title: "Liu–Thom normalization obstructs hyperlinearity of the torsion-free Ollivier–Wise double"
target: fp-torsion-free-nonhyperlinear-group-of-cd-at-most-three
requires:
  - ollivier-wise-kazhdan-rips-construction
  - leavitt-unit-group-finitely-presented
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - openai-nine-leaf-leavitt-configuration
  - leavitt-gl-equals-el-and-perfect-unit-group
  - kazhdan-compression-pairs-normalize-all-tracial-models
artifacts:
  - research/artifacts/torsion-free-nonhyperlinear-rips-double-2026-09-20.md
---

## Credit and sufficient implication

The full proof is in the artifact. The analytic theorem is Jihao Liu's
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2 / 6.7. The conditional normalization and killed-word
double construction are Andreas Thom's
[*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2–1.3, with priority for the conditional implication.
The torsion-free low-dimensional cover is Yann Ollivier and Daniel T.
Wise's [*Kazhdan groups with infinite outer automorphism group*,
Theorem 1.1 and Section 2.1](https://arxiv.org/pdf/math/0409203v1).
The existing Leavitt and finite-presentation prerequisites retain their
own original credits; no new analytic mechanism is asserted here.

The complete nine-leaf code and GL_9=EL_9 identify the ambient Leavitt
pair group with the whole finitely presented unit group Q. Apply
Ollivier–Wise to get `1->N->G->Q->1` with G finitely presented,
torsion-free, `cd_Z G<=2`, and N Kazhdan. The preimage H of the
Leavitt subgroup is Kazhdan, as is G, by extension stability of
property (T). Therefore H is finitely generated. The two compressors
lift, generate G together with H, and preserve the strict nonnormal
infranormal configuration.

In `P=G *_H G`, choose a strict compressor t and `h in H\tHt^-1`.
For any tracial matrix-ultraproduct homomorphism sigma, the normalization
prerequisite applies to the first vertex pair. Since `t_1^-1 t_2`
centralizes H, its conjugate `t_2 t_1^-1` also has image in the H
commutant. Thus sigma kills `[h,t_2 t_1^-1]`. But that word has the
reduced alternating form
```
(h t)_2 (t^-1 h^-1 t)_1 (t^-1)_2,
```
with each syllable outside H. It is nonidentity by the amalgam normal
form theorem. Therefore P is not hyperlinear, rather than merely
nonsofic.

Two finite presentations of G and finitely many identifications of
generators of H present P. Finite subgroups of its Bass–Serre tree
action fix a vertex, so P is torsion-free. Restriction of resolutions
gives `cd_Z H<=2`, and the tree's induced-module exact sequence gives
`cd_Z P<=max(cd_Z G,cd_Z H+1)<=3`. The artifact supplies these
arguments without assuming that H is finitely presented, without
inferring anything from a nonhyperlinear quotient alone, and without
claiming the lower bound `cd_Z P>=3`.

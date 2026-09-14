---
rg: 2
id: cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity-proof
kind: route
title: Proof - recognise the models as Z-action groupoids of subshifts, then apply ring rigidity
target: cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity
requires:
  - orbit-bijective-cocycle-gives-z-action-groupoid
  - subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity
  - crossed-product-el-kazhdan-iff-finite-field-and-subshift
artifacts: [research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md]
---
Details are in the artifact §4. "Theorem C" is `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`.

- **(U) ⇒ (D1).** Theorem C(3) gives G_B ≅ Z ⋉ X, which carries c(n,x) = n.
- **(U) ⇒ (D2).** Theorem C(4).
- **(D1)+(D2) ⇒ (U).** By Theorem C(3) it suffices that every effective ample Hausdorff G with A_{F_2}(G) ≅ R_X is
  isomorphic to Z ⋉ X.
  - Such a G is the model of the Cartan subalgebra given by the image of its diagonal, so by Theorem C(2) it is minimal
    with Cantor unit space.
  - (D1) and `orbit-bijective-cocycle-gives-z-action-groupoid` give G ≅ Z ⋉_T Y, with Y = G^(0) a Cantor set and T a
    minimal homeomorphism. T has no periodic points, since Y is infinite.
  - LC(Y,F_2) ⋊_T Z ≅ R_X is finitely generated, so (Y,T) is conjugate to a subshift, by
    `crossed-product-el-kazhdan-iff-finite-field-and-subshift`.
  - (D2) makes (Y,T) flip conjugate to (X,T_X). A conjugacy, or a flip conjugacy composed with n ↦ −n, induces
    Z ⋉_T Y ≅ Z ⋉ X. ∎

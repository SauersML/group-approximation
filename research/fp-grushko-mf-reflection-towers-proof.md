---
rg: 2
id: fp-grushko-mf-reflection-towers-proof
kind: route
title: Take free powers of the finitely presented absorber and read their Grushko length inside the radical
target: finitely-presented-grushko-towers-with-prescribed-mf-reflection
requires:
  - hilbert-hotel-self-saturated-non-mf
  - compression-defect-dies-in-finite-dimensions
  - mf-radical-product-and-restricted-sum-formulas
  - hilbert-hotel-mf-indistinguishable-thickenings
---

Every map from `A_n` to an MF group restricts trivially to each copy of `B`,
so it is trivial.  Free products of finitely presented groups are finitely
presented, and the abelianization of a free product is the direct sum of the
factor abelianizations.  Since a full-radical group has no nontrivial abelian
quotient, `B` and hence every `A_n` are perfect.  Full radical passes to every
quotient by functoriality.

The compression defect dies in every finite-dimensional linear
representation over every field and normally generates `B`; hence every such
representation of `B`, and therefore of `A_n`, is trivial.  Peter--Weyl
separates points in compact groups by finite-dimensional unitary
representations, so every compact image is trivial as well.

The infinite Kazhdan group `B` has property `FA`, hence is freely
indecomposable and is not infinite cyclic.  Grushko uniqueness makes the
number of copies of `B` in `A_n` an isomorphism invariant.  Property `(T)`
and `FA` give one-endedness of `A_1`; a nontrivial free product of infinite
finitely generated groups has infinitely many ends and its Bass--Serre action
has no global fixed vertex.

For MF `Q`, the product radical formula gives `(GT1)`.  The factorization of
maps gives `(GT2)` and its compact and linear analogues.  Since the MF radical
is characteristic, an isomorphism `E_(n,Q)~=E_(m,Q)` would restrict to
`A_n~=A_m`, forcing `n=m`.

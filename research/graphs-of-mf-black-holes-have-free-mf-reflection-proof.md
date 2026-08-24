---
rg: 2
id: graphs-of-mf-black-holes-have-free-mf-reflection-proof
kind: route
title: Kill the vertex groups and retain exactly the Bass--Serre stable letters
target: graphs-of-mf-black-holes-have-free-mf-reflection
requires:
  - full-mf-radical-groups-form-an-extension-colimit-class
  - mf-equivalences-form-a-colimit-stable-localization
  - hilbert-hotel-self-saturated-non-mf
---

Choose a maximal tree in `Y` and use the standard Bass--Serre presentation of
`Pi`.  Every homomorphism `Pi->M` to an MF group kills every vertex group.
All edge relations then become trivial.  The stable letters indexed by edges
outside the maximal tree are unconstrained, so the homomorphism factors
uniquely through the free group `F_Y`.  Conversely every map from `F_Y`
pulls back along `pi`.  This proves `(BG3)`.

The kernel of `pi` is the normal closure of the vertex groups by the same
presentation.  Since `F_Y` is residually finite and therefore MF, the
factorization identifies this kernel exactly with `Rad_MF(Pi)`, proving
`(BG1)--(BG2)`.

The usual finite graph-of-groups presentation uses finite vertex
presentations, finitely many stable letters, and finitely many edge-generator
identifications.  This gives finite presentation under the stated
hypotheses.  Substituting the finitely presented Hilbert-hotel group at every
vertex gives the final family.

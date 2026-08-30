---
rg: 2
id: stw77-via-colored-centralizer-fusion
kind: route
title: Apply uniform colored centralizer fusion to nuclear-dimension approximations
target: stw99-problem-lxxvii-proper-image-map-oinfty-stable
requires:
  - stw77-properly-infinite-colored-centralizer-fusion
  - oinfty-map-stability-is-central-isometry-splitting
---

## Why sufficient

Let `d=dim_nuc(phi)`.  Given a finite set `F={a_1,...,a_m}` and
`epsilon>0`, the fusion claim supplies a tolerance `eta`.  The definition of
nuclear dimension supplies a `(d+1)`-color approximation to `phi` within
`eta` on `F`.  Fusion then gives exact orthogonal isometries with commutators
below `epsilon`.  Thus `kappa_phi(F)=0` for every finite `F`, and the central
isometry criterion makes `phi` O-infinity-stable.

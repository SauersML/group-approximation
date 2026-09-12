---
rg: 2
id: long-root-central-product-maslov-model-proof
kind: route
title: Separate the central mark in finite rank-one quotients and tensor matching sectors
target: long-root-central-product-has-exact-maslov-models
requires: []
artifacts:
  - research/artifacts/long-root-central-product-maslov-model-2026-08-21.md
---

The two coordinate `SL2(Z)` subgroups commute and intersect trivially in
`Sp4(Z)`.  Their canonical root lifts commute, so their inverse images in
`E_3` commute and intersect in the common kernel `<z>=C3`.  This gives the
displayed central product.

Each inverse image is a finite central extension of the virtually free group
`SL2(Z)`, hence virtually free: pull the extension back to a finite-index free
subgroup and use `H^2(F,C3)=0`.  It is therefore residually finite.  Choose a
finite quotient in which `z` survives.  The `omega^j` eigenspace of `z` in
the quotient's regular representation is nonzero, invariant, and supplies a
finite-dimensional rank-one representation with central character
`z |-> omega^j`.  Tensor the two matching central characters.  The tensor
representation kills `(z,z^(-1))`, descends to `P`, and retains
`rho_j(z)=omega^j I`.


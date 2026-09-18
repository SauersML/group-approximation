---
rg: 2
id: drutu-sapir-bh-via-ascending-hnn-of-free-groups
kind: route
title: The Druţu--Sapir group is an ascending HNN extension of F_2, so the general ascending-HNN theorem embeds it in a simple group of type F_infinity
target: drutu-sapir-group-satisfies-boone-higman
requires:
  - ascending-hnn-of-free-groups-satisfy-boone-higman
  - drutu-sapir-group-index-two-squaring-mapping-torus
---

By (DS0) of `drutu-sapir-group-index-two-squaring-mapping-torus`,
`DS = < x, y, t | t x t^-1 = y^2, t y t^-1 = x >`, which is `F(x,y)*_φ` with
`φ(x) = y^2` and `φ(y) = x`. This `φ` is injective, since its image `<y^2, x>` is free
of rank 2. So `ascending-hnn-of-free-groups-satisfy-boone-higman` applies: `DS` embeds in a simple group of type `F_∞` and lies in
`B_A`. ∎

This route is independent of `drutu-sapir-bh-via-power-map-mapping-tori`. The host here is
BLIW's simple `F_∞` envelope of a generalised Baumslag--Solitar group over `F_2`, not
`Aut_B(B * F_2)`.

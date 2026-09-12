---
rg: 2
id: spherical-artin-bh-via-char-zero-linear-groups
kind: route
title: Spherical Artin groups are linear over Q(x,y), so the characteristic-zero linear root would give them simple envelopes
target: spherical-artin-groups-satisfy-boone-higman
requires:
  - spherical-artin-groups-are-linear-over-q-x-y
  - char-zero-linear-groups-satisfy-boone-higman
---

Let `A(Γ)` be of spherical type.

1. **Linearity.** By `spherical-artin-groups-are-linear-over-q-x-y`, `A(Γ)` is
   isomorphic to a finitely generated subgroup `H <= GL_N(Q(x,y))`. Artin groups
   are finitely generated, and `Q(x,y)` has characteristic zero.
2. **Envelope.** By `char-zero-linear-groups-satisfy-boone-higman`, `H` embeds in
   a finitely presented simple group, and so does `A(Γ)`. QED

Only the case of transcendence degree at most 2 of that root is used.

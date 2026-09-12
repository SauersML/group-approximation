---
rg: 2
id: positive-char-linear-groups-via-leavitt-projective-elementary
kind: route
title: Embed in a simple projective elementary group of a Leavitt tensor power and use its finite presentation
target: positive-char-linear-groups-satisfy-boone-higman
requires:
  - char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
  - leavitt-power-projective-elementary-groups-finitely-presented
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

This is artifact Theorem D. Let `H <= GL_n(K)` be finitely generated, with
`char K = p > 0` and entry field of transcendence degree `d`.

1. `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` gives `N`.
   For every `m >= 2N+1`, `H` embeds in the simple group
   `P_m = E_m(L_p^(⊗d)) / Z`.
2. `leavitt-power-projective-elementary-groups-finitely-presented` gives
   infinitely many `m` with `P_m` finitely presented. Choose one with
   `m >= max(2N+1, 3)`.
3. `H` embeds in the finitely presented simple group `P_m`.

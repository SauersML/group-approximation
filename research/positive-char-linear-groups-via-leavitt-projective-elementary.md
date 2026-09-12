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

1. `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` gives `M_0`.
   For every `M >= M_0`, `H` embeds in the simple group
   `P_M = E_M(L_p^(⊗(d+1))) / Z`.
2. `leavitt-power-projective-elementary-groups-finitely-presented`, at
   `d+1` factors, gives infinitely many `M` with `P_M` finitely presented.
   Choose one with `M >= max(M_0, 3)`.
3. `H` embeds in the finitely presented simple group `P_M`.

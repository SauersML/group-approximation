---
rg: 2
id: binary-cantor-ring-stable-steinberg-group-centrally-closed
kind: claim
title: Over F_2 every Cantor crossed product has K_2 = 0, so its stable elementary group is its Steinberg group and is centrally closed; for minimal X its H_3 is K^0(X,T)/3
distinct_from:
  subshift-elementary-groups-are-steinberg-groups-in-finite-rank: that is the open finite-rank question for EL_n; this is the established stable statement for E = colim EL_n
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

Let `T` be any homeomorphism of a Cantor set `X` and `R_X = LC(X,F_2) ⋊_T Z`. Then:
- `K_2(R_X) = 0`;
- `St(R_X) → E(R_X)` is an isomorphism;
- `H_2(E(R_X);Z) = 0`.

If `(X,T)` is minimal, `H_3(E(R_X);Z) ≅ K_3(R_X) ≅ K^0(X,T)/3K^0(X,T)`.

So the stable elementary group of the note's ring is its own universal central extension, and its third homology is the
dimension group mod 3. For the note's finite-rank group `EL_3(R_X)` the corresponding question is open
(`subshift-elementary-groups-are-steinberg-groups-in-finite-rank`). Unreviewed.

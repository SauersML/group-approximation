---
rg: 2
id: aperiodic-subshift-el-normal-subgroups-are-sandwiched
kind: claim
title: Normal subgroups of EL_n over an aperiodic subshift crossed product are sandwiched by a unique subsystem
distinct_from:
  steinberg-elementary-groups-are-simple-mod-centre: that is the minimal case (normal subgroups central or everything); this classifies the normal subgroups for every aperiodic subshift, up to the K_2 layer
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `aperiodic-subshift-el-normal-subgroups-are-sandwiched-proof`.

Setting:
- X ⊆ A^Z is a subshift without periodic points, R = LC(X,F_2) ⋊ Z, n ≥ 3 and G = EL_n(R).
- For a closed invariant Y ⊆ X, I_Y is the ideal of coefficients vanishing on Y, and π_Y : G → EL_n(LC(Y,F_2) ⋊ Z) is restriction.
- E_Y = E_n(R, I_Y) is the normal closure of the e_ij(I_Y).

Statements:
- (a) For every normal subgroup N ⊴ G there is exactly one closed invariant Y with E_Y ≤ N ≤ ker π_Y. Namely I_Y = {r : e_12(r) ∈ N}.
- (b) ker π_Y / E_Y is the image of K_2(n, LC(Y,F_2) ⋊ Z) = ker(St_n → EL_n). So if that K_2 vanishes, N = ker π_Y.

In words: normal subgroups correspond to subsystems of X, up to a K_2 layer. The note's simplicity theorem is the case Y ∈ {∅, X}.

Without aperiodicity this fails: a periodic orbit contributes congruence subgroups of EL_n(F_2[t^{±1}]).

---
rg: 2
id: subshift-restriction-kernel-is-relative-elementary
kind: claim
title: When the limit sets outside Y ∪ Z lie in Y ∪ Z for a closed invariant Z disjoint from Y, the kernel of EL_n(R_X) → EL_n(R_Y) is E_n(R_X, I_Y)
distinct_from:
  aperiodic-subshift-ring-unstable-k2-vanishes: that asks for vanishing of K_2(n,R_Y) for every aperiodic Y; this proves the kernel equality (equivalently surjectivity of K_2(n,R_X) → K_2(n,R_Y)) under a limit-set condition, with no information about K_2(n,R_Y)
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `subshift-restriction-kernel-relative-elementary-proof`.

Setting:
- X ⊆ A^Z is a subshift, Y ⊆ X is closed invariant, and n ≥ 2.
- Suppose there is a closed invariant Z ⊆ X∖Y with α(x) ∪ ω(x) ⊆ Y ∪ Z for every x ∈ X∖(Y ∪ Z).

Conclusions:
- ker(EL_n(R_X) → EL_n(R_Y)) = E_n(I_Y) = E_n(R_X, I_Y).
- For n ≥ 3, K_2(n,R_X) → K_2(n,R_Y) is onto. For any ring, ideal I and n ≥ 3, (EL_n(R) ∩ GL_n(R,I))/E_n(R,I) ≅ coker(K_2(n,R) → K_2(n,R/I)).

Y and Z may be minimal subshifts. Nothing about their unstable K_2 is used.

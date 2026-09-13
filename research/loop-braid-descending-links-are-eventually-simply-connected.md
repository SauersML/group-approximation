---
rg: 2
id: loop-braid-descending-links-are-eventually-simply-connected
kind: claim
title: "The descending links L_n(LB_*) of the loop braid cloning system are simply connected for all large n"
artifacts:
  - research/artifacts/zp-loop-braid-descending-links-model-2026-09-13.md
---

There is N such that for every n ≥ N the complex `L_n(LB_*)` (Witzel–Zaremsky,
arXiv:1405.5491v3, §5.3, for the loop braid system of §10) is simply connected.
This is the n = 2 case of `loop-braid-descending-links-are-increasingly-connected`.

## Attempts

- 2026-09-13 (lane z2-12-loop-bv), structure (artifact §§1–2):
  - `L_n(LB_*)` is connected for `n ≥ 5`, by the proof of WZ Lemma 5.10.
  - `PΣAut_n` acts with a strict fundamental domain isomorphic to the ordered
    matching complex `OM(K_n)`. The stabilizers are conjugates
    `s·(PLB_{n−m})κ_Γ·s^{-1}` of cabling subgroups.
- Dead: complete join over `OM(K_n)` (artifact §3; the invariant
  `f = e_13 − e_23 − e_14 + e_24` shows two fusion bands can clasp).
- Plan (artifact §4):
  - Reduce to `PΣAut_n = colim` of the cabling subgroups over `OM(K_n)`, via the
    complex-of-groups criterion for strict fundamental domains (statement to
    verify).
  - Prove the colimit presentation from McCool's presentation.
  - The one delicate point is pinning the cable-twist power in the images of
    `α_ij` under cloning.

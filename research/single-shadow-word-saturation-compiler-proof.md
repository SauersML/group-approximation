---
rg: 2
id: single-shadow-word-saturation-compiler-proof
kind: route
title: Higman-envelope one bug, make its normal closure suitable, and route the output through it
target: single-shadow-word-saturation-compiler
requires:
  - op-to-hs-shadow-residual-functoriality
  - mikaelian-explicit-higman-embedding
  - common-quotient-onto-normal-subgroup
  - hyperlinear-killed-normal-kazhdan-mf-transfer
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

Embed `G` in a finitely presented `H`; functoriality preserves the nontrivial
shadow word.  Put `E=H*F_2`.  The factor embedding preserves the word again,
while the Bass--Serre action makes `E` non-elementary acylindrically
hyperbolic with trivial finite radical.  The normal closure `N=<<w>>^E` is
infinite because its conjugates by powers of a free generator are distinct.
It is therefore a suitable normal reservoir.

Apply `common-quotient-onto-normal-subgroup` to `E` and a fixed finitely
presented hyperbolic Kazhdan group, protecting `w`.  The output is 2-generated,
finitely presented, AH, Kazhdan, nontrivial, and satisfies `q(N)=Q`.
Functoriality gives `Q=q(N)<=S(Q)`, hence `S(Q)=Q`.  The normal-Kazhdan
detector gives `normMFResidual Q=top`.  Lean checks the analytic endpoint as
`normMFResidual_eq_top_of_shadow_bug_saturation`; Higman, Bass--Serre/Osin,
and Hull are the stated external group-theoretic inputs.

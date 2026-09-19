---
rg: 2
id: defect-saturation-from-single-shadow-word
kind: route
title: Saturate the one HNN shadow commutator instead of the preassembled defect subgroup
target: defect-saturation-full-mf-radical
requires:
  - fournier-facio-hnn-single-shadow-bug
  - single-shadow-word-saturation-compiler
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

The HNN seed is already finitely presented, torsion-free, and AH, so apply
the torsion-free branch of the one-word compiler directly to
`N=<<[s,x]>>`.  Protect `[s,x]`, route every output generator through two
reservoir elements of `N`, and take the common quotient with a torsion-free
hyperbolic Kazhdan group.  Then `q(N)=Q`, the word survives, and `Q` is
2-generated, finitely presented, torsion-free, AH, Kazhdan, and full
MF-radical.  This route uses only one shadow word from the compression
calculation; it does not first identify or saturate the whole simple-factor
defect.

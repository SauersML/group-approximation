---
rg: 2
id: biasymptotic-subshift-complement-ideal-is-ultramatricial
kind: claim
title: If every point outside a subsystem Y has both limit sets in Y, the ideal I_Y of LC(X,F_2)⋊Z is a union of finite matrix subrings over F_2
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `biasymptotic-complement-ideal-ultramatricial-proof`.

Setting:
- X ⊆ A^Z is a subshift and Y ⊆ X is closed and invariant.
- Suppose α(x) ∪ ω(x) ⊆ Y for every x ∈ X∖Y.

Conclusion: every finite subset of I_Y = {Σ f_j u^j : supp f_j ∩ Y = ∅} lies in a subring with a unit e_V that is isomorphic to a finite product of matrix rings M_k(F_2). So `ultramatricial-ideals-have-elementary-congruence-kernels` applies to I_Y.

The limit-set hypothesis is what makes this work: a corner e_V R e_V whose V meets a recurrent orbit outside Y is not locally finite.

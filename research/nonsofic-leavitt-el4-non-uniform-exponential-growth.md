---
rg: 2
id: nonsofic-leavitt-el4-non-uniform-exponential-growth
kind: claim
title: The nonsofic Kazhdan group EL_4 over the binary Leavitt algebra has non-uniform exponential growth
artifacts:
  - research/artifacts/sk-verify-14-2026-09-13-part4.md
---

**ESTABLISHED (unreviewed; sk-free-8).** Let `L = L_(F_2)(1,2) = F_2⟨s_0,s_1,t_0,t_1 | t_i s_j = δ_ij, s_0t_0 + s_1t_1 = 1⟩`. For every `n ≥ 3`, `EL_n(L)` has non-uniform exponential growth. In particular `EL_4(L)`, which is nonsofic with property (T) (`universal-leavitt-el4-nonsofic`), is a nonsofic Kazhdan group of non-uniform exponential growth.

Route: `nonsofic-leavitt-el4-non-uniform-exponential-growth-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: the matrix units `s_i t_j`, the corner isomorphism `a ↦ s_0 a t_0`, and `L ≅ M_2(L)`. The hypotheses of the self-similar ring theorem hold. The kernel-checked nonsofic import is over `BinaryLeavittAlgebra (ZMod 2) = RingQuot (Relation k)`, whose five relations (`UniversalLeavittOver.lean` l.38–49) are exactly those of `L`. See `research/artifacts/sk-verify-14-2026-09-13-part4.md` §6.

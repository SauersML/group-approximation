---
rg: 2
id: binary-tensor-square-defect-left-support-proof
kind: route
title: The tensor-square image of the defect has off-diagonal left support, which is a null norm idempotent
target: binary-tensor-square-rank-functions-kill-two-root-defect
requires:
  - binary-tensor-square-rank-functions-live-on-diagonal-norms
  - leavitt-rank-functions-killing-two-root-defect-are-augmentation
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

Artifact Theorem 2.4.
1. **The defect:** `Δ_2(D) = e_23 ⊗ e_12 + e_12 ⊗ e_23`, and `Sym(p_[10], p_[0]) · Δ_2(D) = Δ_2(D)`.
2. **Nullity:** `Sym(p_[10], p_[0])` is null by Proposition 2.2 of the artifact. The two sets are disjoint and
   their union misses `[11]`. So `rk Δ_2(D) = 0`.
3. **Conclusion:** the pullback along `Δ_2` is a rank function on `F_2[R^x]` killing `D`. By
   `leavitt-rank-functions-killing-two-root-defect-are-augmentation` it is the augmentation rank.

*Verification by `w3-vf-linear` (2026-09-12), Section 27.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Δ_2(D) = e_12⊗e_23 + e_23⊗e_12 (using e_23 e_12 = 0), and Sym(p_[10], p_[0]) Δ_2(D) = Δ_2(D) since p_[10]e_12 = p_[0]e_23 = 0; the norm is null and the pullback is rk_ε by Section 23.1.*

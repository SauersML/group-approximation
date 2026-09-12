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
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

Artifact Theorem 2.4.
1. **The defect:** `Δ_2(D) = e_23 ⊗ e_12 + e_12 ⊗ e_23`, and `Sym(p_[10], p_[0]) · Δ_2(D) = Δ_2(D)`.
2. **Nullity:** `Sym(p_[10], p_[0])` is null by Proposition 2.2 of the artifact. The two sets are disjoint and
   their union misses `[11]`. So `rk Δ_2(D) = 0`.
3. **Conclusion:** the pullback along `Δ_2` is a rank function on `F_2[R^x]` killing `D`. By
   `leavitt-rank-functions-killing-two-root-defect-are-augmentation` it is the augmentation rank.

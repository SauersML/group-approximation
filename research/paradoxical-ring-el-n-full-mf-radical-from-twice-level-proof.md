---
rg: 2
id: paradoxical-ring-el-n-full-mf-radical-from-twice-level-proof
kind: route
title: One-sided inverse with full complement in M_n(R), rank-two theorem, block embedding, signed permutations
target: paradoxical-ring-el-n-full-mf-radical-from-twice-level
requires:
  - full-defect-ring-non-mf-at-rank-two
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Full derivation in the artifact, §2.

1. **Full complement in `S = M_n(R)`.** Fix `θ : R^n → R^n ⊕ P` with `P = R ⊕ Q`, and put `s = θ^{-1}ι` and `t = πθ`.
   Then `ts = 1`, and `e = 1 − st` has image `≅ P`. With `α : P → R`, `β : R → P` (`αβ = 1`),
   `x_i = ε_i α π_P θ` and `y_i = θ^{-1} ι_P β δ_i`, we get `x_i e y_i = e_ii`. Hence `1 = Σ x_i e y_i ∈ SeS`.
2. **Rank two.** `full-defect-ring-non-mf-at-rank-two` applied to `S` makes every homomorphism `EL_2(S) → MF`
   trivial.
3. **Blocks.** For `N ≥ 2n`, the corner embedding `M_2(S) → M_N(R)` maps `EL_2(S)` into `EL_N(R)`. The image of
   `e_12(X)` is `Π_{a,b} e_{a,n+b}(X_ab)`, and its factors commute.
4. **Normal generation.** A homomorphism `φ : EL_N(R) → MF` kills `e_{1,n+1}(r)`, the image of `e_12(r E_11)`, for all
   `r`. Conjugating by signed permutations `w_kl = e_kl(1) e_lk(−1) e_kl(1)` gives every `e_ij(±r)`, so `φ` is trivial.

---
rg: 2
id: subshift-el-groups-boundedly-elementary-generated-proof
kind: route
title: End-local Fredholm corrections of tower compressions give a block-diagonal factor with banded inverse; the remainder is block-diagonal for midpoint towers; finite block Gauss reduction bounds each factor by 39
target: subshift-el-groups-boundedly-elementary-generated
requires: []
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md
---

The full proof is Theorem D in part 3, §§1–2. It is self-contained: Kakutani–Rokhlin partitions, linear algebra over `F_2`, and Thompson's theorem (Trans. AMS 101 (1961) 16–33) that every element of `SL_n(K)`, `n ≥ 3`, is a commutator.

- **(T1)** For `S = ∏_a M_{h_a}(F_2)` with `h_a ≥ 3`, every element of `GL_3(S)` is a product of at most 39 elementary matrices.
  - `sr(S) = 1` gives 9 elementary matrices down to `diag(p,q,r)`.
  - Two Whitehead diagonals (6 each) reduce to `diag(1,1,v)`.
  - `v = [x,y]` componentwise by Thompson, and `diag(1,1,[x,y])` is 3 Whitehead diagonals.
- **(T2)** Half-line compressions `P h_x P` are Fredholm, the index is additive, and it vanishes on root elements (`Q² = I` up to finite rank), hence on `G`.
- **(T3)** At one cut, a correction `F` supported in a window of width `2w` makes `Q + F` bijective, with `(Q+F)^{-1} = P h^{-1} P + D` and `D` supported in a window of width `8w`. The choice of `F` depends only on the local configuration.
- **(T4)** For a block of length `≥ 32w`, `P_B h P_B + F_top + F_bot` has inverse `P_B h^{-1} P_B + D_top + D_bot`, checked column by column in the upper and lower halves.
- **Assembly.** Take towers of height `≥ 64w` with atoms refined to fix the local types. Then `H_1 = ⊕ A_B ∈ GL_3(A_𝒫)`, and `H_1^{-1}h − I` is supported within `14w` of the cuts (sk-verify-16 F1; was 12w). So `H_2 := H_1^{-1}h ∈ GL_3(A_𝒫′)` for the towers based at midpoint levels, and `h = H_1H_2` needs at most `39 + 39 = 78` elementary matrices.

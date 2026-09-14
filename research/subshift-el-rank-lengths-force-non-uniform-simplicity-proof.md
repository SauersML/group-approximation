---
rg: 2
id: subshift-el-rank-lengths-force-non-uniform-simplicity-proof
kind: route
title: Sylvester rank is invariant under units and subadditive; single-entry matrices have the rank of their entry; the measure of a small clopen set tends to zero
target: subshift-el-rank-lengths-force-non-uniform-simplicity
requires: [cantor-z-crossed-product-embeds-in-continuous-factor, finite-model-subshift-elementary-groups-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

The full proof is Theorem A in part 1, §1.

- **Rank function.** Ara–Claramunt (required claim) give a faithful Sylvester matrix rank function `rk_μ` on `R` for ergodic `μ`, with `rk_μ(χ_U) = μ(U)`. It extends to `M_3(R)` with `rk_μ(I_3) = 3`.
- **Invariance.** `rk(xay) = rk(a)` for invertible `x, y`, since `rk(ab) ≤ min(rk a, rk b)`. So `ℓ_μ(xgx^{-1}) = rk_μ(x(g−I)x^{-1}) = ℓ_μ(g)` and `ℓ_μ(g^{-1}) = rk_μ(−g^{-1}(g−I)) = ℓ_μ(g)`.
- **Subadditivity.** `gh − I = (g−I)h + (h−I)` and `rk(a+b) ≤ rk a + rk b`.
- **Faithfulness** is that of `rk_μ`.
- **Root elements.** `r E_ij = (r E_ii)·Π` with `Π` a permutation matrix, and `rk_μ(r E_ii) = rk_μ(r ⊕ 0 ⊕ 0) = rk_μ(r)`.
- **Lower bound.** Item 3 follows from items 1 and 2. With `h = e_12(1)` and `g = e_12(χ_V)` it gives `ν ≥ 1/μ(V)` for every ergodic `μ`.
  - The supremum over ergodic measures is the supremum over `M_T(X)`: `μ ↦ 1/μ(V)` is quasi-affine, so its extrema on the simplex are attained at extreme points.
  - `μ` is nonatomic because `X` is infinite and minimal, so clopen `V` with `μ(V) → 0` exist.
- **Simplicity** of `G` for infinite minimal subshifts is the required claim `finite-model-subshift-elementary-groups-simple-kazhdan-lef` (the note's tower proof, with `Γ = Z`).

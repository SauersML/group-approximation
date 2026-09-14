---
rg: 2
id: finite-models-transvection-covering-converges-to-measure-proof
kind: route
title: Rank subadditivity below, permutation conjugates of the diagonal idempotent plus one commutator above, and periodic-orbit measures supported on X in the limit
target: finite-models-transvection-covering-converges-to-measure
requires: [transvection-normal-generation-recovers-invariant-measures, finite-simple-groups-converge-to-simple-kazhdan-group]
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part2.md
---

The full proof is Theorem B_fin in part 2, §1.

- **Lower bound.** Rank over `F_2` is conjugation-invariant and subadditive, and `rk(e_12(P) − I) = rk P`. So `N ≤ νm`.
- **Upper bound.** Cut `Z/N` into `⌊N/m⌋` groups of size `m` and a remainder of size `r < m`.
  - A permutation matrix `σ` moves the support of `D_ℓ(χ_V)` onto a group, and `diag(σ,σ,σ^{−2}) ∈ SL_{3N}(F_2)` conjugates `e_12(D_ℓ(χ_V))` to `e_12(P_t)`.
  - The remainder is `[e_13(P′), e_32(P″)]` with `P″ ⊇ P′` a rank-`m` coordinate projection. That is 2 conjugates, since `e_32` is a permutation conjugate of `e_12`.
- **Limits.** `m_ℓ/N_ℓ = η_ℓ([V])` for the periodic-orbit measure `η_ℓ` of `y_ℓ`. Cylinders of words outside `L(X)` get measure `0` once `2ℓ+1` exceeds their length. So weak* limits are shift-invariant and supported on `X`.
- **Comparison with `G_X`** is the required transvection formula. The required marked-limit claim supplies the models.

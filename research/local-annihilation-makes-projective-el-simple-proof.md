---
rg: 2
id: local-annihilation-makes-projective-el-simple-proof
kind: route
title: A locally annihilated noncommuting root turns a noncentral element into a one-column matrix and then a root
target: local-annihilation-makes-projective-el-simple
requires: []
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
  - GroupApproximation/Pestov91/SimpleModCentre.lean
---

Certified in Lean: `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`, root-imported from
`GroupApproximation.lean`. Paper proof in artifact §3:

1. Let `N ⊴ EL_n(R)` and `g ∈ N` noncentral. The coefficients `s` whose roots all commute with `g` form a non-unital
   subring. So local annihilation, applied to the entries of `g`, gives a root `h = e_ij(s)` not commuting with `g`,
   with `t ≠ 0`, `ts = 0` and `t g_pk s = 0`.
2. `ρ = g h g⁻¹ h⁻¹ ∈ N`, `ρ ≠ 1`, and `t(ρ − 1) = 0`.
3. Simplicity gives `c` with `(ρ − 1)_qm c t ≠ 0`. The commutator `[ρ, e_ml(ct)]` is a one-column matrix, and column
   extraction gives a nonzero root in `N`.
4. The level ideal of `N` is nonzero, hence `R`, so `N = EL_n(R)`.

Centre: a central `g` commutes with every `e_ij(1)` and `e_ij(a)`, so `g = λI` with `λ ∈ Z(R)^×`.

---
rg: 2
id: subshift-el-root-elements-boundedly-normally-generated-proof
kind: route
title: The note's tower commutator lands in a finite simple GL_d(F_2), the transvection formula produces e_12(1), and a commutator identity produces every root element
target: subshift-el-root-elements-boundedly-normally-generated
requires: [transvection-normal-generation-recovers-invariant-measures, finite-model-subshift-elementary-groups-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

The full proof is Corollary C in part 1, §3.

- **Tower step.** The simplicity proof (required claim) gives, for `g ≠ e`, a tower transvection `x` with `k = [g,x] ≠ e`. So `k` is a product of 2 conjugates of `g^{±1}`, and it lies in the embedded copy `H ≅ GL_d(F_2)` over a small clopen `V_g`, with `d ≥ 3`.
  - `H` is finite simple, so the transvection `e_12(χ_{V_g}) ∈ H` is a product of at most `c_H < ∞` conjugates of `k^{±1}`.
  - So `M′_g ≤ 2c_H`.
- **Unit transvection.** The required transvection formula with `U = X` writes `e_12(1)` with at most `2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3 ≤ 2⌊1/inf_μ μ(V_g)⌋ + 2` conjugates of `e_12(χ_{V_g})`.
- **All root elements.** `e_ij(r) = [e_ik(r), e_kj(1)]` is 2 conjugates of `e_kj(1)^{±1}`, and `e_kj(1)` is a permutation-matrix conjugate of `e_12(1)` in `SL_3(F_2) ⊆ G`.
- **Norms.**
  - A conjugate of `g` is a product of `λ^c(g) < ∞` conjugates of root elements, since `G = E_3(R)`.
  - A conjugate of a root element is a product of `M_g` conjugates of `g^{±1}`.

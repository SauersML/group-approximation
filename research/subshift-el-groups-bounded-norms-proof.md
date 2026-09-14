---
rg: 2
id: subshift-el-groups-bounded-norms-proof
kind: route
title: At most 78 root elements per element, 2 conjugates of e_12(1) per root element, and the transvection formula for e_12(1)
target: subshift-el-groups-have-bounded-conjugation-invariant-norms
requires: [subshift-el-groups-boundedly-elementary-generated, subshift-el-root-elements-boundedly-normally-generated, subshift-el-rank-lengths-force-non-uniform-simplicity]
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md
---

Part 3, §3.
1. **Boundedness.** A conjugation-invariant norm satisfies `‖h‖ ≤ 78·sup_r ‖e_ij(r)‖ ≤ 156‖e_12(1)‖`, since `e_ij(r) = [e_ik(r), e_kj(1)]` and `e_kj(1)` is a permutation conjugate of `e_12(1)`.
2. **Finite `N_g`.** `N_g ≤ 156·M′_g`, where `M′_g` conjugates of `g^{±1}` give `e_12(1)` (required root-element claim).
3. **Transvections.** For `g = e_12(χ_V)`, `M′_g ≤ 2⌊1/inf_μ μ(V)⌋ + 2` by the transvection formula with `U = X`. The lower bound is the rank-length claim.

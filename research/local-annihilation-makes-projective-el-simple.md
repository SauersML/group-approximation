---
rg: 2
id: local-annihilation-makes-projective-el-simple
kind: claim
title: Over a simple ring with local annihilation, every normal subgroup of EL_n (n >= 3) is central or everything
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
  - GroupApproximation/Pestov91/SimpleModCentre.lean
---

**ESTABLISHED (Lean on main, root-imported; paper proof unreviewed).** Let `R` be a unital simple ring with local
annihilation: for every finite `F ⊆ R`, the elements `s` admitting `t ≠ 0` with `ts = 0` and `tfs = 0` for all
`f ∈ F` generate `R` as a non-unital ring. Let `n ≥ 3`. Then every normal subgroup of `EL_n(R)` is central or all of
`EL_n(R)`. So `EL_n(R)/Z(EL_n(R))` is simple, and `Z(EL_n(R)) ⊆ Z(R)^× I_n`.

Lean: `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`
(`hcard : 3 ≤ Fintype.card ι`, `[IsSimpleRing R]`, `hloc : LocalAnnihilation R`). No sandwich theorem and no
stable-range or exchange hypothesis is used.

This is the common ring criterion behind the simplicity halves of the Pestov 9.1 answer (via
`localAnnihilation_of_crossedProduct`) and of the Leavitt unit groups: L_k(1,d) is a Steinberg algebra, see
`steinberg-algebras-have-local-annihilation`.

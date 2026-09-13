---
rg: 2
id: steinberg-elementary-groups-are-simple-mod-centre-proof
kind: route
title: Ring simplicity, local annihilation and scalar centre feed the Lean ring criterion; EJZ adds (T)
target: steinberg-elementary-groups-are-simple-mod-centre
requires:
  - steinberg-algebra-simple-iff-minimal-effective
  - steinberg-algebras-have-local-annihilation
  - local-annihilation-makes-projective-el-simple
  - minimal-effective-steinberg-algebras-have-scalar-centre
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

Artifact §4.
1. `R = A_k(𝒢)` is simple (`steinberg-algebra-simple-iff-minimal-effective`).
2. `R` has local annihilation (`steinberg-algebras-have-local-annihilation`: compact infinite unit space).
3. By `local-annihilation-makes-projective-el-simple`, normal subgroups of `EL_n(R)` are central or everything, and
   `Z(EL_n(R)) ⊆ Z(R)^× I_n = k^× I_n` by `minimal-effective-steinberg-algebras-have-scalar-centre`.
4. `S_n` is infinite. `R` is infinite-dimensional, since an infinite compact totally disconnected space has infinitely
   many disjoint clopens. If `e_12(a) e_12(b)⁻¹ = e_12(a−b)` is central, then `a = b`.
5. For finite `k` and finitely generated `R`, `EL_n(R)` has (T) (`elementary-groups-over-fg-rings-have-property-t`).
   (T) passes to the quotient `S_n`, and (T) groups are finitely generated.

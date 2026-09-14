---
rg: 2
id: rf-groups-embed-in-simple-kazhdan-lef-groups-proof
kind: route
title: Put the group inside the derived subgroup of an RF overgroup, take the Toeplitz Kazhdan envelope of the overgroup, and use Whitehead's lemma
target: rf-groups-embed-in-simple-kazhdan-lef-groups
requires:
  - rf-groups-lie-in-derived-subgroups-of-rf-groups
  - rf-toeplitz-subshifts-over-residually-finite-groups
  - residually-finite-group-toeplitz-elementary-groups-lef-kazhdan
  - minimal-effective-steinberg-algebras-have-scalar-centre
artifacts:
  - research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md
---

Artifact §5.

1. **Reduction to infinite `Γ`.** If `Γ` is finite, replace it by `Γ × Z`, which is finitely generated, residually
   finite and infinite.
2. **Overgroup.** `rf-groups-lie-in-derived-subgroups-of-rf-groups` gives a finitely generated, infinite, residually
   finite `Δ` and an injective `ρ : Γ -> Δ` with `ρ(Γ) ≤ [Δ,Δ]`.
3. **Envelope.**
   - Let `X_Δ` be the RF Toeplitz subshift (`rf-toeplitz-subshifts-over-residually-finite-groups`) and
     `R = LC(X_Δ,F_2) ⋊ Δ`.
   - By `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` with `q = 2`, `N = 3`, the group
     `EL_3(R)/Z(EL_3(R))` is infinite, finitely generated, simple, Kazhdan and LEF.
   - By `minimal-effective-steinberg-algebras-have-scalar-centre`, `Z(EL_3(R)) ≤ F_2^× I = {I}`, so `G = EL_3(R)` is
     that group.
4. **Whitehead.** Over any ring, for a unit `c`: `w(c) = e_12(c) e_21(−c^(-1)) e_12(c) = [[0,c],[−c^(-1),0]]` and
   `w(c)w(−1) = diag(c,c^(-1))`, so `diag(c,c^(-1)) ∈ E_2`. For units `a, b`:
   `diag(a,a^(-1)) diag(b,b^(-1)) diag((ba)^(-1),ba) = diag(aba^(-1)b^(-1), 1)`. So `diag([a,b],1,1) ∈ E_3(R)`. This
   is steps 1–2 of `perfect-unit-subgroups-elementary-proof`.
5. **Embedding.**
   - `δ ↦ u_δ` is an injective homomorphism `Δ -> R^×`, so `γ ↦ ψ(γ) = diag(u_(ρ(γ)),1,1)` is an injective
     homomorphism `Γ -> GL_3(R)`.
   - Each `ρ(γ)` is a product of commutators in `Δ`, so `ψ(γ)` is a product of matrices `diag([u_a,u_b],1,1) ∈ E_3(R)`.
   - Hence `ψ : Γ -> G` is an injective homomorphism. ∎

A self-contained simplicity proof over `Δ` (the note's tower argument with balls) uses freeness at every point,
`rf-toeplitz-subshifts-act-freely`. That proof is written out in the artifact, §4.

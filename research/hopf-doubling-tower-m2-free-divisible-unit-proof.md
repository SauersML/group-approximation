---
rg: 2
id: hopf-doubling-tower-m2-free-divisible-unit-proof
kind: route
title: Mod-2 Chern classes kill every square subbundle, while block halving divides the unit on faces
target: hopf-doubling-tower-has-no-m2-but-divides-unit-tracially
requires:
  - block-balanced-towers-have-central-halving
  - central-halving-trivializes-every-closed-bauer-face-bundle
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Section 4 of the artifact (Corollary D).

1. **No square subbundle.** Let `e ⊥ f` be equivalent projections in `A_n`, with range
   bundle `F`.
   - Then `q_n ≅ F ⊕ F ⊕ G`.
   - Mod 2, `c(F ⊕ F) = c(F)² = Σ_i c_i(F)²`.
   - Every positive-degree class squares to zero in
     `H*((S²)^M; F_2) = F_2[e_1, …, e_M]/(e_c²)`, with `M = 2^{n−1}`.
   - So `c(G) = c(q_n) = Π_c (1 + e_c)`. Its top term `e_1 ⋯ e_M ≠ 0` forces
     `rank G ≥ M = rank q_n`, hence `F = 0`.
2. **The limit.** A nonzero `*`-homomorphism `M_2 → A` is a partial isometry `v` with
   `v*v ⊥ vv* ≠ 0`.
   - `M_2` is semiprojective, so such a `v` exists in `μ_n(A_n)` for some `n`.
   - The maps are injective, which contradicts step 1.
3. **Face divisibility.**
   - The two blocks `π_1*q_n` and `π_2*q_n` have rank `2^{n−1}`, so the tower is
     block-balanced with `L = 2^{n−m}`.
   - AH limits are nuclear, and `rank q_n → ∞` with injective maps rules out
     finite-dimensional representations.
   - The second prerequisite gives relative divisibility for every `N` and every closed
     `K ⊆ ∂_e T(A)`.

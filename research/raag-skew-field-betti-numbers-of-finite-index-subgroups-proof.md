---
rg: 2
id: raag-skew-field-betti-numbers-of-finite-index-subgroups-proof
kind: route
title: Mayer--Vietoris over lifted maximal tori of the Salvetti cover; tori are acyclic over the division ring and vertices contribute the nerve
target: raag-skew-field-betti-numbers-of-finite-index-subgroups
requires: []
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
---

Complete proof in `research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md`,
Section 1, Steps 1--5. Outline.

1. For `Λ ≅ Z^k`, `k ≥ 1`, and a division ring `D ⊇ F[Λ]`, `H_*(Λ; D) = 0`: the Koszul
   complex is the cone of right multiplication by `1 − w_1`, which is a chain
   automorphism because `1 − w_1` is invertible in `D` and commutes with every `1 − w_j`.
2. Cover the finite cover `X̂` of the Salvetti complex by the components of the preimages
   of the maximal tori `T_σ`. An intersection of components is a union of components of
   the preimage of `T_τ`, `τ` the intersection of the simplices, which is `D`-acyclic when
   `τ ≠ ∅` and a set of vertices when `τ = ∅`.
3. The Mayer--Vietoris spectral sequence has only the row `j = 0`, and that row is
   `⊕_{vertices x̂} D ⊗ C_*(Δ, N)`, with `Δ` the full simplex on the maximal simplices of `L`
   and `N ≃ L` their nerve. So `H_p(H; D) = D^{#vertices} ⊗ H̃_{p−1}(L; F)` and `X̂` has
   `[A_L : H]` vertices.

Checked on `L` a point (`Z`), two points (`F_2`, Euler characteristic) and a simplex (`Z^k`).

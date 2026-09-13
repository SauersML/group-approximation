---
rg: 2
id: infinite-subgroup-invariant-zero-outer-entropy-proof
kind: route
title: The span of vectors fixed by an infinite subgroup is singular with the regular representation, so Seward's theorem kills its entropy
target: infinite-subgroup-invariant-information-has-zero-outer-entropy
requires: [koopman-lambda-singular-part-has-zero-rokhlin-entropy, seward-rokhlin-entropy-subadditivity]
artifacts:
  - research/artifacts/symmetry-kills-rokhlin-information-2026-09-12.md
---

Complete proof: Theorem S of the artifact.

1. **The subspace.** `H` is the closed span of `ρ(g) ξ` over `g` in `G` and `ξ` in `L²_0(X)^Λ`. It is
   `ρ(G)`-invariant.
2. **Singularity.** Let `σ <= H` be a subrepresentation embedding into `λ`, with projection `P` commuting with
   `ρ(G)`.
   - `Pξ` is `Λ`-invariant. A `Λ`-invariant vector in `ℓ²(G)` is constant on infinite cosets, so it is `0`.
   - So `P` kills a spanning set of `H` and `σ = 0`. The converse direction reduces to the same statement.
   - This is singularity in Seward's sense: "no non-zero sub-representation of one embeds into the other".
3. **Vanishing.** Every `Λ`-invariant set `B` gives `1_B - mu(B)` in `H`, so `F_Λ ⊆ σ-alg(H)`.
   `koopman-lambda-singular-part-has-zero-rokhlin-entropy` gives `h_G(σ-alg(H)) = 0`, and outer entropy is
   monotone.
4. **Ergodic equality.** `seward-rokhlin-entropy-subadditivity` gives `h^Rok_G(X) <= 0 + h_G(X | F_Λ)`, and the
   reverse inequality is immediate.

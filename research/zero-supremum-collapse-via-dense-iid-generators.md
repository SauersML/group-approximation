---
rg: 2
id: zero-supremum-collapse-via-dense-iid-generators
kind: route
title: Density of generating i.i.d. partitions at zero supremum gives isomorphic Bernoulli shifts by the Baire category theorem
target: zero-rokhlin-supremum-forces-bernoulli-collapse
requires:
  - iid-generators-dense-at-zero-rokhlin-supremum
---

Let `G` be countably infinite with `h^Rok_sup(G) = 0`. Take `K = {0,1} × {0,1,2}` and `L = {0,1}`, both
uniform, so that `H(κ) = log 6 ≠ log 2 = H(λ)`. Notation of the prerequisite.

1. **Non-empty and complete.**
   - The partition of `X` by the first factor of the coordinate at `1_G` lies in `Ind_λ(X)`.
   - `L`-labelled partitions modulo null sets, with `d(ξ, ζ) = µ(ξ ≠ ζ)`, form a complete metric space.
   - The conditions `µ(ξ_ℓ) = λ(ℓ)` and `µ(∩_(i <= n) g_i·ξ_(ℓ_i)) = ∏_i λ(ℓ_i)`, for distinct
     `g_1, …, g_n`, are continuous in `d`. So `Ind_λ(X)` is closed, hence complete.
2. **Open sets.** Fix a countable family `𝒬` of finite partitions of `X` generating `B(X)` as a σ-algebra.
   For `Q ∈ 𝒬` and `m >= 1` put

       U_(Q,m) = { ξ ∈ Ind_λ(X) : H(Q | ξ^W) < 1/m for some finite W ⊆ G }.

   For fixed `W`, changing `ξ` on a set of measure `δ` changes `ξ^W` on a set of measure at most `|W|δ`. So the
   joint distribution of `Q` and `ξ^W` moves continuously, and `ξ ↦ H(Q | ξ^W)` is continuous. Hence
   `U_(Q,m)` is open.
3. **Density.** Let `ξ ∈ Ind_λ(X)` generate. Along finite `W_n ↑ G`, `H(Q | ξ^(W_n)) → H(Q | σ-alg_G(ξ)) = 0`,
   so `ξ` lies in every `U_(Q,m)`. By the prerequisite the generating partitions are dense in `Ind_λ(X)`, so
   every `U_(Q,m)` is dense.
4. **Baire.** `∩_(Q,m) U_(Q,m)` is a countable intersection of dense open subsets of the complete space
   `Ind_λ(X)`. So it contains some `ξ`, and `H(Q | σ-alg_G(ξ)) = 0` for every `Q ∈ 𝒬`. So `ξ` generates.
5. **Isomorphism.** Define `x ↦ (g ↦ the ℓ with g^-1 x ∈ ξ_ℓ)`.
   - It is equivariant.
   - It pushes `µ` to `λ^G`, by independence of the translates.
   - It is injective almost everywhere, because `ξ` generates.

   So `6^G ≅ 2^G`, and `log 3 = log 6 − log 2` lies in `D(G) \ {0}`.

The same argument for any two finite bases with an i.i.d. partition of the second inside the first gives the
finite-entropy part of the strong form.

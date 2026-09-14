---
rg: 2
id: lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts-proof
kind: route
title: The lamplighter host over the half-line overgroup is simple Kazhdan LEF, contains the group, and its word problem reduces to the group's
target: lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts
requires: [half-line-overgroup-keeps-lef-and-solvable-word-problem, groups-embed-in-derived-subgroup-of-half-line-overgroup, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef, crossed-product-el-word-problem-is-group-wp-plus-language]
artifacts:
  - research/artifacts/sk-decidable-host-2026-09-13.md
---

**(⇐)** Write a finite generating set of `Γ` as words in the generators of the host. Triviality of a word in `Γ` is
triviality of its translation, so `WP(Γ)` is solvable. LEF passes to subgroups.

**(⇒)**
1. **Overgroup.** `Δ = C(Γ)` is infinite and finitely generated, and `Γ ≅ δ_0(Γ) ≤ [Δ,Δ]`
   (`groups-embed-in-derived-subgroup-of-half-line-overgroup`). It is LEF with `WP(Δ) ≡_T WP(Γ)`
   (`half-line-overgroup-keeps-lef-and-solvable-word-problem`).
2. **Host.** `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ` acts on `Ω = 2^Δ`, `R = LC(Ω,F_2) ⋊ L`, and `G = EL_3(R)`. By
   `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`, `G` is infinite, finitely generated, simple, Kazhdan
   and LEF, and `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L] ⊇ [Δ,Δ] ⊇ Γ` in `G`.
3. **Subshift form.** `F_x(ℓ) = (ℓ^(-1)x)(e)` is an `L`-equivariant homeomorphism of `Ω` onto an `L`-subshift
   `X ⊆ F_2^L`. It is injective since `F_x(δ) = x(δ)` for `δ ∈ Δ`, and the letter indicator is `{x : x(e) = 1}`. By
   `crossed-product-el-word-problem-is-group-wp-plus-language`, `WP(G) ≡_T WP(L) ⊕ L(X)`.
4. **`WP(L) ≤_T WP(Δ)`.** Normal forms `(c, δ)` in `F_2^(⊕Δ) ⋊ Δ`, with lamp positions compared through `WP(Δ)`.
5. **`L(X) ≤_T WP(Δ)`.** For `ℓ = (c,δ)` acting by `x ↦ δx + c`, `(ℓ^(-1)x)(e) = x(δ) + c(δ)`. A pattern `p` on a
   finite `W ⊆ L` occurs iff the constraints `x(δ_w) = p(w) + c_w(δ_w)` agree whenever `δ_w = δ_(w')`. Consistent
   constraints are realized, since `Ω` is the full shift, and all tests use `WP(Δ)`.

So `WP(G)` is solvable. Details and model tests: artifact §4 and §6.

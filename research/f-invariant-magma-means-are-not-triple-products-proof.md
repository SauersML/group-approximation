---
rg: 2
id: f-invariant-magma-means-are-not-triple-products-proof
kind: route
title: Re-association invariance on rectangles forces the middle factor of a triple product to be idempotent
target: f-invariant-magma-means-are-not-triple-products
requires:
  - free-binary-systems-carry-no-idempotent-mean
---

Notation is as in the target. `^ : T × T → T` is injective, and `A^B = {a^b : a ∈ A, b ∈ B}`. All integrals are of
bounded functions against means, so every step uses only finite additivity and the definition of `μ^ν`.

**Fact R (rectangles).** `μ^ν(A^B) = μ(A)ν(B)`. For `s ∈ A` the section `(A^B)_s` is `B`, by injectivity, and for
`s ∉ A` it is empty.

**Lemma 1.** Let `γ = β^κ` and `κ = β′^κ′` for means `β, κ, β′, κ′`. Suppose `γ(D_1) = 1` and `γ` is
`x_1`-invariant. Then `β(T^T) = 1`, `β = β^β′` and `κ = κ′`.

*Proof.*
- *Domain.* `γ(D_1) = γ((T^T)^T) = β(T^T)κ(T) = β(T^T)` by Fact R. So `β(T^T) = 1`.
- *Left factor.* Let `Y ⊆ T^T` and `W = Y^T ⊆ D_1`. Then `γ(W) = β(Y)` by Fact R.
  - By injectivity, `x_1·W = {a^(b^c) : a^b ∈ Y, c ∈ T}`. Its section at `a` is `Y_a^T`, with `Y_a = {b : a^b ∈ Y}`.
  - So `γ(x_1·W) = ∫ κ(Y_a^T) dβ(a)`. By Fact R, `κ(Y_a^T) = β′(Y_a)κ′(T) = β′(Y_a)`. Hence
    `γ(x_1·W) = ∫ β′(Y_a) dβ(a) = β^β′(Y)`.
  - Invariance gives `β(Y) = β^β′(Y)` for every `Y ⊆ T^T`.
  - Both `β` and `β^β′` give full measure to `T^T`: `β` by the domain step, and `β^β′` because it is supported on
    products. So `β = β^β′` on every set.
- *Right factor.* Let `C ⊆ T` and `W = (T^T)^C`. Then `x_1·W = T^(T^C)`. By Fact R and `β(T^T) = 1`,
  `γ(W) = κ(C)` and `γ(x_1·W) = κ(T^C) = β′(T)κ′(C) = κ′(C)`. So `κ = κ′`. ∎

**Lemma 2.** If `γ = β^κ`, `γ(D_2) = 1` and `γ` is `x_2`-invariant, then `κ(D_1) = 1` and `κ` is `x_1`-invariant.

*Proof.*
- *Domain.* `γ(D_2) = γ(T^D_1) = κ(D_1)` by Fact R.
- *Invariance.* For `V ⊆ D_1`, put `W = T^V ⊆ D_2`. Then `x_2·W = T^(x_1·V)`. So `γ(W) = κ(V)` and
  `γ(x_2·W) = κ(x_1·V)`. ∎

**Proof of the theorem.** Suppose `γ = β^(β′^κ)` is F-invariant, and put `κ₁ = β′^κ`.
1. Lemma 1, applied with `(β, κ, β′, κ′) = (β, κ₁, β′, κ)`, gives `κ₁ = κ`. So `κ = β′^κ`.
2. Lemma 2 gives `κ(D_1) = 1` and `κ` is `x_1`-invariant.
3. Now `κ = β′^κ` and `κ = β′^κ`, so Lemma 1 applies to `γ := κ` with `(β, κ, β′, κ′) = (β′, κ, β′, κ)`. It gives
   `β′ = β′^β′`.
4. So `β′` is an idempotent mean on the free magma `T`. That contradicts
   `free-binary-systems-carry-no-idempotent-mean`. ∎

**Hypotheses actually used.**
- From `x_2`-invariance only the product-set tests `T^V` are used. From `x_1`-invariance only `Y^T` and `(T^T)^C`.
- Both domain conditions are used: `β(T^T) = 1` and `β′(T^T) = 1`. The latter comes from `κ(D_1) = 1` via Fact R,
  and it is what extends `β′ = β′^β′` from `T^T` to all sets.
- So the theorem also holds for the weaker notion of invariance on product-shaped sets alone.

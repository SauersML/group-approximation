---
rg: 2
id: fg-full-group-subgroups-subshift-factor-proof
kind: route
title: Refining the cocycle level sets lets the generators act on the coding factor by the same rules
target: fg-full-group-subgroups-factor-onto-subshift-full-groups
requires: []
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

## Why sufficient

1. **Coding map.**
   - Each cell of `P` is clopen, so `π_P` is continuous.
   - `π_P(λx)(μ) = cell(μλ·x) = π_P(x)(μλ) = (λ·π_P(x))(μ)`, so `π_P` is equivariant.
   - So `X_P = π_P(X)` is compact and invariant, i.e. a subshift.
   - The cell of `x` itself is `π_P(x)(e)`.
2. **Rules.**
   - `c_i` is constant on cells, so `c_i(x) = d_i(π_P(x)(e))` for a map `d_i : P -> Λ`.
   - Put `ḡ_i(z) = d_i(z(e))·z` for `z ∈ X_P`. It is continuous, with a locally constant
     cocycle.
   - Then `π_P(g_i x) = π_P(c_i(x)·x) = c_i(x)·π_P(x) = ḡ_i(π_P x)`.
   - So `ḡ_i` maps `X_P` onto `X_P`, since `π_P` and `g_i` are onto.
   - Define `ḡ'_i` from `c'_i` the same way. Then `ḡ'_i ∘ ḡ_i ∘ π_P = π_P ∘ g_i^{-1} ∘ g_i = π_P`,
     and `π_P` is onto, so `ḡ'_i ∘ ḡ_i = id`. Likewise `ḡ_i ∘ ḡ'_i = id`.
   - So `ḡ_i ∈ [[Λ ~ X_P]]`.
3. **Homomorphism.**
   - By induction on length, every word `w` in the letters `s_i^{±1}` satisfies
     `π_P ∘ w(g) = w(ḡ) ∘ π_P`.
   - If `w(g) = id_X`, then `w(ḡ) ∘ π_P = π_P`, so `w(ḡ) = id` because `π_P` is onto.
   - So `g_i -> ḡ_i` defines a surjective homomorphism `θ_P`. This proves item 1.
4. **Nontriviality.**
   - `ḡ_i(π_P x) = π_P(c·x)`, whose value at `e` is the cell of `c·x`, while `π_P(x)(e)` is
     the cell of `x`.
   - These differ when a cell separates `x` from `c·x`, and they stay different in any finer
     partition. This proves item 2.
5. **Simple case.** `ker θ_P` is normal in `Γ`, and it is not all of `Γ` by step 4. So it is
   trivial, and `Γ ≅ Γ_P`, which is infinite, so `X_P` is infinite. This proves item 3.
6. **Inherited dynamics.**
   - A factor of a minimal system is minimal.
   - Pushforwards of invariant measures are invariant.
   - A nonempty open `U ⊆ X_P` has nonempty open preimage, so full support passes to the
     pushforward.
   - `λx = x` implies `λ·π_P x = π_P(λx) = π_P x`, so stabilizers grow.
   - This proves item 4.
7. **Abelian case.**
   - For abelian `Λ`, `μ·Fix(λ) = Fix(μλμ^{-1}) = Fix(λ)`, so `Fix(λ)` is closed and
     invariant.
   - By minimality of `X_P` it is empty or `X_P`. So `K = {λ : Fix(λ) = X_P}` is the
     stabilizer of every point, and `Λ/K` acts freely.
   - A colouring `z` fixed by `K` satisfies `z(μk) = z(μ)`, so it is a colouring of `Λ/K`,
     and `X_P` is a subshift over `Λ/K`.
   - Cocycles into `Λ` project to `Λ/K`. Conversely, a locally constant cocycle into `Λ/K`
     lifts through any set-theoretic section, so the two full groups agree.
   - `X_P` is infinite and minimal, so `Λ/K` is infinite. This proves item 5.

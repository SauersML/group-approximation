---
rg: 2
id: bernoulli-rokhlin-entropy-orbit-relation-invariance-proof
kind: route
title: Bernoulli labels ride on the orbit, the full group moves only the root, and generation relative to the base is a full-group notion
target: bernoulli-rokhlin-entropy-is-an-orbit-relation-invariant
requires:
  - seward-weak-containment-relative-entropy-equality
  - abert-weiss-free-actions-weakly-contain-bernoulli
artifacts:
  - research/artifacts/bernoulli-bundle-orbit-relation-entropy-2026-09-17.md
---

Full details are in Sections 1 and 2 of the artifact. The shift is `(gξ)(k) = ξ(g^{-1}k)`, and
`κ(y, z)` is the unique k with `z = k·y`.

**Item 1.**

1. *Invariant sets.* `L^G` is weakly mixing, so `L^2_0(L^G) ⊗ π` has no invariant vectors for any π.
   Hence `I_G ⊆ B(Y)`, and `E_λ = inf{H(α | B(Y)) : σ-alg_G(α) ∨ B(Y) = B(L^G × Y)}`.
2. *Labellings.* `(ξ, y) ↦ (y, ℓ)` with `ℓ(z) = ξ(κ(y, z)^{-1})` on `G·y`. A direct check gives
   `ℓ_{(gξ, gy)} = ℓ_{(ξ,y)}`, so G moves only the root, and λ^G becomes the product measure on the orbit.
3. *Full group.* For φ in [R_Y], `φ̃(ξ, y) = (g_φ(y)ξ, φy)`, that is `φ̃(y, ℓ) = (φy, ℓ)`. This is a
   measure-preserving automorphism, agreeing with g on `L^G × Y_g`.
4. *Generation.* `𝒜 = σ-alg_G(α) ∨ B(Y)` contains every `L^G × Y_g`, and
   `φ̃(A) = ⋃_g (gA ∩ (L^G × gY_g))`. So 𝒜 is the smallest [R_Y]-invariant sigma-algebra containing α
   and B(Y).
5. *Transport.* For an orbit equivalence θ, set `Θ(y, ℓ) = (θy, ℓ∘θ^{-1})`, that is `η(h) = ξ(c(h, y))`
   with `θ^{-1}(h^{-1}θy) = c(h, y)^{-1}y`. For fixed y, `h ↦ c(h, y)` is a bijection H → G, so Θ is a
   measure-preserving isomorphism fibered over θ with `Θ(B(Y)) = B(Z)`. It conjugates φ̃ to
   `(θφθ^{-1})~`. It therefore preserves the generation condition of step 4 and the conditional entropy,
   and the infima agree.

**Item 2.** If λ is a point mass, both sides are 0. Otherwise `L^G` is essentially free: a point fixed by
`g ≠ 1` is constant on an infinite ⟨g⟩-orbit, or on infinitely many independent finite ones. Take
`Y = [0,1]^G`, or any free action weakly contained in all free actions. Such actions exist by
`abert-weiss-free-actions-weakly-contain-bernoulli` (arXiv:1103.1063v2, Theorem 1: every free action
weakly contains every Bernoulli action). `seward-weak-containment-relative-entropy-equality`
(arXiv:1602.06680v2, Theorem 1.2) applies with X = `L^G` and F trivial:

    h_G(X | F) = h_G(X × Y | F ∨ B(Y)).

The ergodic shift has trivial I_G, so the left side is `h^Rok_G(L^G, λ^G)`.

**Item 3.** A generating partition β of `L^Γ` generates `L^Γ × W` relative to B(W), with
`H(β | B(W)) <= H(β)`. The Rokhlin entropy of a Bernoulli shift is at most H(λ), using the partition by
the 1-coordinate when H(λ) < ∞ (otherwise the bound is trivial).

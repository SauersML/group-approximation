---
rg: 2
id: thompson-t-dirichlet-space-restricted-symplectic-model
kind: claim
title: "In the smoothed piecewise-PSL_2(Z) model, Thompson's T acts on the Dirichlet space H^{1/2}(S^1)/R through the restricted symplectic group, and the area cocycle of its displacement cocycle is minus the Euler cocycle up to a coboundary"
distinct_from:
  thompson-t-is-isomorphic-to-ppsl2z: that is the abstract isomorphism with PPSL_2(Z); this adds C^1 regularity at the breakpoints, Weil-Petersson class, and the Hilbert-Schmidt condition on the Dirichlet space
  cup-products-of-integrably-paired-potential-cocycles-are-exact: Step 3 of its proof route computes the Euler class as the area of the displacement cocycle for PL T on periodic PL functions; this puts the same cocycle in a Hilbert symplectic space on which T acts by restricted symplectic maps, which PL T does not do (corners are not Weil-Petersson)
  lifted-thompson-t-euler-class-in-kahler-subspace: that asks for a unitary representation with Euler area class; here the representation is symplectic and only Hilbert-Schmidt close to unitary
artifacts: []
---

**ESTABLISHED** by `thompson-t-dirichlet-space-restricted-symplectic-model-proof`.

**Setting.**
- `H = H^{1/2}(R/Z)/R`, the real Dirichlet space of mean-zero functions, with symplectic form
  `ω(φ, ψ) = ∫_0^1 φ dψ = −2πi Σ_n n φ̂_n ψ̂_{−n}` and complex structure `J` equal to the Hilbert
  transform, `(Jφ)^_n = −i sgn(n) φ̂_n`. Then `⟨φ, ψ⟩ = ω(φ, Jψ) = 2π Σ_n |n| φ̂_n \bar{ψ̂_n}` is the
  Dirichlet inner product, and `ω(Jφ, Jψ) = ω(φ, ψ)`.
- `ψ₀ : RP^1 → R/Z`, `ψ₀(x) = arctan(x)/π`, is a real-analytic diffeomorphism. Let `T` act on
  `R/Z` by `g ↦ ψ₀ g ψ₀^{-1}`, `g ∈ PPSL_2(Z) ≅ T` (`thompson-t-is-isomorphic-to-ppsl2z`). Call
  this the *smoothed model*. `E` is the group of lifts to `R` of these homeomorphisms. It is a
  central extension of `T` by `⟨z⟩`, `z(x) = x + 1`, isomorphic as an extension to `T̄` up to
  the sign of `z`.

**Statement.**
1. Every element `h` of the smoothed model is a `C^1` diffeomorphism of `R/Z` with `log h'`
   Lipschitz, hence of Weil–Petersson class.
2. `ρ(g)φ = φ ∘ g^{-1}` defines a homomorphism `ρ : T → Sp(H, ω)` with `[ρ(g), J]`
   Hilbert–Schmidt for every `g`.
3. With `u_f = f̃ − id` for a lift `f̃`, the map `c(g) = u_{g^{-1}}` (mod constants) is a 1-cocycle
   `T → H` for `ρ`, and its area cocycle is
   `Ω(g, h) = ω(c(g), ρ(g)c(h)) = ω(u_g ∘ h̃, u_h) = −D(g, h)`, where
   `D(g, h) = ∫_0^1 (u_g(h̃x) − u_g(x)) dx`. For a normalized section `σ` of `E → T`,
   `Ω = −ε + dβ_A` with `β_A(g) = ∫_0^1 u_{σ(g)}`. So `[Ω] = −e_R`.

Hence `(T, E, H, ω, J, ρ, c)` satisfies the setting of
`symplectic-gaussian-actions-split-area-cocycles` with `a = −1`.

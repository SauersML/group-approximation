---
rg: 2
id: kazhdan-mean-free-amenable-residually-finite-proof
kind: route
title: Almost invariant densities give almost invariant square roots, the Kazhdan gap pushes them onto finite orbits, and a nontrivial finite orbit is a finite quotient
target: kazhdan-groups-mean-free-amenable-iff-residually-finite
requires:
  - mean-free-amenable-actions-residually-amenable-and-sofic
---

Notation as in the claim. `D` is the set of `ℓ¹` densities on `Ω`, `(s·f)(ω) = f(s^-1 ω)`, and
`(sξ)(ω) = ξ(s^-1 ω)` on `ℓ²(Ω)`.

**Item 1.**
- **(a) A good net.** Let `m` be an invariant mean on `Ω`.
  - For a finite `Φ ⊆ ℓ∞(Ω)` and `δ > 0`, let `D_(Φ,δ) = {f ∈ D : |f(φ) - m(φ)| < δ for φ ∈ Φ}`. It is
    convex. `m` lies in its weak*-closure, because `D` is weak*-dense among means (step (a) of the
    companion proof) and `D_(Φ,δ)` is the intersection of `D` with a weak*-neighbourhood of `m`.
  - As in step (b) of the companion proof, the affine map `f ↦ (s·f - f)_(s ∈ Q)` sends a net in
    `D_(Φ,δ)` converging weak* to `m` to a net converging weakly to `0` in `⊕_(s ∈ Q) ℓ¹(Ω)`. By Mazur's
    lemma there is `f ∈ D_(Φ,δ)` with `Σ_(s ∈ Q) ‖s·f - f‖₁ < ε`.
  - Indexing by `(Φ, δ, ε)` gives a net `f_α ∈ D` with `f_α → m` weak* and
    `ε_α = Σ_(s ∈ Q) ‖s·f_α - f_α‖₁ → 0`.
- **(b) Square roots.** `ξ_α = √f_α` is a unit vector in `ℓ²(Ω)`. Since `|√a - √b|² ≤ |a - b|` for
  `a, b ≥ 0`, we get `‖sξ_α - ξ_α‖₂² ≤ ‖s·f_α - f_α‖₁`, so `max_(s ∈ Q) ‖sξ_α - ξ_α‖₂ ≤ √ε_α`.
- **(c) The Kazhdan gap.** Let `P` be the orthogonal projection onto the invariant vectors `H^G` in
  `ℓ²(Ω)`.
  - `(H^G)^⊥` is invariant and contains no nonzero invariant vector. By the Kazhdan pair, every unit
    vector `η` in it has `max_(s ∈ Q) ‖sη - η‖ ≥ κ`.
  - Write `ξ = Pξ + ξ^⊥`. Then `sξ - ξ = sξ^⊥ - ξ^⊥`, so `‖ξ^⊥‖ ≤ max_(s ∈ Q) ‖sξ - ξ‖ / κ`.
- **(d) Invariant vectors live on finite orbits.** An invariant vector is constant on orbits and square
  summable, so it vanishes on infinite orbits. So `H^G ⊆ ℓ²(Ω_fin)`, hence
  `ξ·1_(Ω \ Ω_fin) = (ξ - Pξ)·1_(Ω \ Ω_fin)` and `‖ξ·1_(Ω \ Ω_fin)‖ ≤ ‖ξ^⊥‖`.
- **(e) Conclusion.** `f_α(Ω \ Ω_fin) = ‖ξ_α·1_(Ω \ Ω_fin)‖² ≤ ε_α / κ² → 0`. Weak* convergence at the
  single function `1_(Ω \ Ω_fin)` gives `m(Ω \ Ω_fin) = 0`, i.e. `m(Ω_fin) = 1`.

**Item 2.**
- **(⇒)** Let `(Ω, m)` be a mean-free amenable action and `g ≠ e`. By item 1, `m(Ω_fin) = 1`, while
  `m(Fix(g)) = 0`. So `Ω_fin ⊄ Fix(g)`: some finite orbit `O` contains a point moved by `g`. The action on
  `O` is a homomorphism `G → Sym(O)` into a finite group, and `g` maps to a nontrivial element. So `G` is
  residually finite.
- **(⇐)** A residually finite group is residually amenable, so item 1 of
  `mean-free-amenable-actions-residually-amenable-and-sofic` gives a mean-free amenable action.

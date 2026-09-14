---
rg: 2
id: mean-free-amenable-actions-residually-amenable-and-sofic-proof
kind: route
title: Quotient towers give mean-free means, Day's convexity trick plus a layer-cake level set gives almost-free Følner sets, and amenable stabilizers transfer invariant means to the group
target: mean-free-amenable-actions-residually-amenable-and-sofic
requires: []
---

Notation as in the claim. For `f ∈ ℓ¹(Ω)` and `s ∈ G` put `(s·f)(ω) = f(s^-1 ω)`, so that
`(s·f)(φ) = f(φ∘s)` for `φ ∈ ℓ∞(Ω)`. Invariance of a mean on indicators extends by linearity and norm
density of simple functions to `m(φ∘s) = m(φ)` for all `φ ∈ ℓ∞(Ω)`.

**Item 1.**
- **The tower.** Enumerate `G \ {e} = {g_1, g_2, ...}`. For each `i` choose a normal subgroup `N_i` with
  `G/N_i` amenable and `g_i ∉ N_i`. Put `M_n = N_1 ∩ ... ∩ N_n`. Then `G/M_n` embeds in
  `∏_(i ≤ n) G/N_i`, a finite product of amenable groups, so `G/M_n` is amenable.
- **The space.** Let `Ω = ⊔_n G/M_n`, with `G` acting on each piece by left multiplication. Let `m_n` be
  a left-invariant mean on the group `G/M_n`, viewed on `ℓ∞(Ω)` through restriction to the `n`-th piece.
  It is `G`-invariant, since `g` acts on `G/M_n` as left multiplication by `gM_n`.
- **The mean.** For a nonprincipal ultrafilter `U` on `N`, `m(φ) = lim_U m_n(φ|_(G/M_n))` is an invariant
  mean on `Ω`.
- **Mean-freeness.** Let `g = g_i`. For `n ≥ i`, `g ∉ M_n`. On `G/M_n`, `g·xM_n = xM_n` iff
  `x^-1 g x ∈ M_n` iff `g ∈ M_n`, by normality. So `Fix(g) ∩ G/M_n = ∅` for all `n ≥ i`, and
  `m(Fix(g)) = lim_U m_n(∅) = 0`.

**Item 2.** `m` is invariant under `H`, and `Fix(h)` is the same set for the restricted action.

**Item 3.**
- **(a) Densities are dense.** Let `D = {f ∈ ℓ¹(Ω) : f ≥ 0, Σ f = 1}`. Every mean `m` lies in the
  weak*-closure of `D`. Otherwise Hahn–Banach gives a real `φ ∈ ℓ∞` and `c` with
  `m(φ) > c ≥ f(φ)` for all `f ∈ D`. Taking point masses, `sup φ ≤ c < m(φ) ≤ sup φ`, a contradiction.
- **(b) Day's trick.** Fix a finite `K ⊆ G` and `ε > 0`. Consider the affine map
  `T : D → E = (⊕_(s ∈ K) ℓ¹(Ω)) ⊕ R^(K \ {e})`, `T(f) = ((s·f - f)_(s ∈ K), (f(Fix(g)))_(g ∈ K \ {e}))`.
  - Take a net `f_α ∈ D` with `f_α → m` weak*. For `φ ∈ ℓ∞`,
    `(s·f_α - f_α)(φ) = f_α(φ∘s - φ) → m(φ∘s) - m(φ) = 0`, and `f_α(Fix(g)) → m(Fix(g)) = 0`.
  - The dual of `E` is `(⊕ ℓ∞) ⊕ R^(K \ {e})`, so `T(f_α) → 0` weakly in `E`. Hence `0` is in the weak
    closure of the convex set `T(D)`, which is its norm closure by Mazur's lemma.
  - So some `f ∈ D` has `Σ_(s ∈ K) ‖s·f - f‖₁ + Σ_(g ∈ K \ {e}) f(Fix(g)) ≤ ε`.
- **(c) A level set.** For `t > 0` put `E_t = {f > t}`, a finite set because `f ∈ ℓ¹`. For nonnegative
  `u, v ∈ ℓ¹` and `Y ⊆ Ω`, the layer-cake formula gives:
  - `‖u - v‖₁ = ∫_0^∞ |{u > t} Δ {v > t}| dt`;
  - `u(Y) = ∫_0^∞ |{u > t} ∩ Y| dt`;
  - `‖u‖₁ = ∫_0^∞ |{u > t}| dt`.

  Since `{s·f > t} = sE_t`, the integrand
  `I(t) = Σ_s |sE_t Δ E_t| + Σ_g |E_t ∩ Fix(g)| - ε|E_t|` satisfies `∫_0^∞ I(t) dt ≤ ε - ε = 0`.
  `I(t) = 0` when `E_t = ∅`, and `E_t ≠ ∅` for all `t` in `(0, max f)`, a set of positive measure. So
  some `t` has `E_t ≠ ∅` and `I(t) ≤ 0`. Put `A = E_t`.
- **(d) Sofic maps.** For `s ∈ G` the partial injection `A ∩ s^-1 A → A`, `a ↦ sa`, extends to a
  bijection `σ(s)` of `A`. Note `|A \ s^-1 A| = |sA \ A| ≤ |sA Δ A|`.
  - **Multiplicativity.** Let `g, h, gh ∈ K`. If `a ∈ A`, `ha ∈ A` and `gha ∈ A`, then
    `σ(g)σ(h)a = gha = σ(gh)a`. The exceptions are at most `|A \ h^-1 A| + |A \ g^-1 A| + |A \ (gh)^-1 A|
    ≤ 3ε|A|` points.
  - **Few fixed points.** Let `g ∈ K \ {e}`. If `σ(g)a = a`, then either `ga ∈ A`, so `ga = a` and
    `a ∈ Fix(g)`, or `a ∉ g^-1 A`. So `σ(g)` fixes at most `2ε|A|` points.
  - **Soficity.** Letting `K` exhaust `G` and `ε → 0` gives maps `σ` that are asymptotically
    multiplicative on every finite set, with `d(σ(g), id) → 1` for every `g ≠ e`. That is soficity.

**Item 4.**
- **Setup.** Suppose `G` is not amenable, and `m` is an invariant mean on `Ω` with `m(Y) > 0`, where
  `Y = {ω : Stab(ω) amenable}`. `Y` is `G`-invariant, because stabilizers along an orbit are conjugate.
  Then `m_Y(φ) = m(φ·1_Y)/m(Y)` is an invariant mean on `Y`.
- **Transfer map.** Choose orbit representatives `R ⊆ Y` and, for `ω ∈ R`, a left-invariant mean `μ_ω`
  on `H_ω = Stab(ω)`. Define `P : ℓ∞(G) → ℓ∞(Y)` by `(Pφ)(gω) = μ_ω(h ↦ φ(gh))` for `ω ∈ R`, `g ∈ G`.
  - **Well defined.** If `gω = g'ω` then `g' = gk` with `k ∈ H_ω`, and
    `μ_ω(h ↦ φ(gkh)) = μ_ω(h ↦ φ(gh))` by left invariance of `μ_ω`.
  - **Positive, unital, equivariant.** With `(x·φ)(y) = φ(x^-1 y)` on both sides,
    `P(x·φ)(gω) = μ_ω(h ↦ φ(x^-1 g h)) = (Pφ)(x^-1 gω) = (x·Pφ)(gω)`.
- **Conclusion.** `M(φ) = m_Y(Pφ)` is a left-invariant mean on `G`, since
  `M(x·φ) = m_Y(x·Pφ) = m_Y(Pφ)` by invariance of `m_Y`. So `G` is amenable, a contradiction.

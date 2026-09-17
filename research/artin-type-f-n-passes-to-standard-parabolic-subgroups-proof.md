---
rg: 2
id: artin-type-f-n-passes-to-standard-parabolic-subgroups-proof
kind: route
title: "Proof: the Godelle–Paris retraction gives a 1-Lipschitz retraction A_Γ → A_T, and Rips filtrations transfer F_n"
target: artin-type-f-n-passes-to-standard-parabolic-subgroups
requires: []
---

Notation. `A = A_Γ` with generators `σ_s` (`s ∈ S`), `W` the Coxeter group, `A_T` the
Artin group of `Γ_T` (defined by its own presentation), `θ : A_T → A` the map
`σ_t ↦ σ_t`. Word metrics: `d_S` on `A` for `{σ_s^{±1}}`, `d_T` on `A_T` for
`{σ_t^{±1} : t ∈ T}`. Words are finite sequences `σ_{s_1}^{ε_1} ⋯ σ_{s_ℓ}^{ε_ℓ}`.

## 1. Imported facts (Charney–Paris, arXiv:1401.7634, Section 2)

Read from the LaTeX source on 2026-09-17.

- (Salvetti complex.) `Sal(Γ)` is a CW complex with vertex set `{x(u) : u ∈ W}`, edges
  `a(u, s)` oriented from `x(u)` to `x(us)`; `W` acts freely, and `BSal(Γ) = Sal(Γ)/W` has
  one vertex `x_0` and one oriented loop `ā_s` for each `s ∈ S`, with
  `π_1(BSal(Γ), x_0) = A` (the loop `ā_s` is `σ_s`; Proposition 2.4). The embedding
  `W_T × 𝒮_T^f ↪ W × 𝒮^f` induces an embedding `ι_T : Sal(Γ_T) ↪ Sal(Γ)`.
- (Theorem 2.5, Godelle–Paris.) "The embedding ι_T : Sal(Γ_T) ↪ Sal(Γ) admits a
  retraction π_T : Sal(Γ) → Sal(Γ_T)."
- (Lemma 2.6.) "Let u ∈ W. Write u = u_0u_1, where u_0 ∈ W_T and u_1 is (T, ∅)-minimal.
  Then (1) π_T(x(u)) = x(u_0). (2) Let s ∈ S and set t = u_1 s u_1^{-1}. If t ∈ T, then
  π_T(a(u,s)) = a(u_0,t). If t ∉ T, then π_T(a(u,s)) = x(u_0)."

## 2. The word map (Charney–Paris, proof of Theorem 1.2)

Let `α̂ = σ_{s_1}^{ε_1} ⋯ σ_{s_ℓ}^{ε_ℓ}` be a word. Put `u_i = s_1 ⋯ s_i ∈ W`, write
`u_i = v_i w_i` with `v_i ∈ W_T` and `w_i` `(T, ∅)`-minimal. Put `t_i = w_{i−1} s_i
w_{i−1}^{−1}` if `ε_i = 1` and `t_i = w_i s_i w_i^{−1}` if `ε_i = −1`, and
`τ_i = σ_{t_i}^{ε_i}` if `t_i ∈ T`, `τ_i = 1` (empty word) otherwise. Set
`τ̂(α̂) = τ_1 ⋯ τ_ℓ`, a word in the generators of `A_T`.

(a) `lg τ̂(α̂) ≤ lg α̂`, and `τ_i` depends only on `s_1, …, s_i`, so
`τ̂(α̂ σ_s^{ε}) = τ̂(α̂) τ_{ℓ+1}` with `lg τ_{ℓ+1} ≤ 1`.

(b) Let `γ(α̂)` be the lift, starting at `x(1)`, of the loop `ā_{s_1}^{ε_1} ⋯ ā_{s_ℓ}^{ε_ℓ}`
of `BSal(Γ)`. It is the edge path `a_1^{ε_1} ⋯ a_ℓ^{ε_ℓ}` with `a_i = a(u_{i−1}, s_i)` if
`ε_i = 1` and `a_i = a(u_i, s_i)` if `ε_i = −1`. By Lemma 2.6, `π_T(a_i)` is an edge of
`Sal(Γ_T)` lying over `ā_{t_i}` when `t_i ∈ T`, and a vertex otherwise; hence
`π_T(γ(α̂)) = γ_T(τ̂(α̂))`, the lift in `Sal(Γ_T)` from `x(1)` of the loop of `τ̂(α̂)`
(Charney–Paris state exactly this: "π_T(γ(α̂)) = γ(τ̂)").

(c) If `α̂` uses only letters from `T`, then `τ̂(α̂) = α̂` (Claim 1 there: all `u_i ∈ W_T`,
so `w_i = 1`, `t_i = s_i ∈ T`).

## 3. A 1-Lipschitz retraction `r : A → A_T`

**Well-definedness.** Let `α̂, α̂'` be words representing the same `α ∈ A`. Their loops in
`BSal(Γ)` are homotopic rel `x_0`, so the lifts `γ(α̂)`, `γ(α̂')` (same start `x(1)`) are
homotopic rel endpoints in `Sal(Γ)` (homotopy lifting for the covering `Sal(Γ) → BSal(Γ)`).
Applying the continuous map `π_T` and 2(b), `γ_T(τ̂(α̂))` and `γ_T(τ̂(α̂'))` are homotopic
rel endpoints in `Sal(Γ_T)`. Projecting to `BSal(Γ_T)`, whose fundamental group is `A_T`
(Proposition 2.4 for `Γ_T`), the words `τ̂(α̂)` and `τ̂(α̂')` represent the same element of
`A_T`. So `r(α) :=` the element of `A_T` represented by `τ̂(α̂)` is well defined.

**Retraction.** For `β ∈ A_T` choose a word `β̂` in `T`; it represents `θ(β)` in `A`, and by
2(c) `r(θ(β)) = β`. So `r ∘ θ = id_{A_T}`. In particular `θ` is injective (van der Lek's
theorem, recovered), and below `A_T` is identified with `θ(A_T) ⊆ A`.

**Lipschitz.** If `d_S(α, α') = 1`, then `α' = α σ_s^{ε}`; take `α̂` for `α` and `α̂ σ_s^{ε}`
for `α'`. By 2(a), `r(α') = r(α) · (τ_{ℓ+1})` with `τ_{ℓ+1}` of length at most 1, so
`d_T(r(α), r(α')) ≤ 1`. By the triangle inequality along a geodesic,
`d_T(r(α), r(α')) ≤ d_S(α, α')` for all `α, α' ∈ A`.

**Comparison.** For `β, β' ∈ A_T`, a `T`-word for `β^{−1}β'` is an `S`-word, so
`d_S(β, β') ≤ d_T(β, β')`; with the Lipschitz bound and `r|_{A_T} = id`,
`d_S = d_T` on `A_T` (this is the convexity half of Charney–Paris; it is not needed below).

## 4. Brown's criterion for Rips filtrations

For a group `G` with a finite generating set and word metric `d`, and an integer `R ≥ 1`,
let `VR_R(G)` be the simplicial complex with vertex set `G` whose simplices are the finite
nonempty subsets of diameter at most `R`. Let `Δ(G)` be the full simplex on `G` (all finite
nonempty subsets). Left multiplication acts simplicially; `Δ(G)` is contractible and
`VR_1 ⊆ VR_2 ⊆ ⋯` exhausts it.

- The barycentric subdivision `sd Δ(G)` is a `G`-CW complex: a cell stabilizer fixes its
  cell pointwise, since it fixes the chain of subsets defining the cell.
- The stabilizer of a cell `F_0 ⊊ ⋯ ⊊ F_p` preserves the finite set `F_p ⊆ G` and acts
  freely on `G`, so it embeds in `Sym(F_p)` and is finite, hence of type `F_∞`.
- `sd VR_R(G)` is `G`-cocompact: every simplex is a translate of one containing `1`, and
  those lie in the finite ball of radius `R`.

Brown's criterion (K. S. Brown, *Finiteness properties of groups*, J. Pure Appl. Algebra 44
(1987), Corollary 3.3; cited, not re-read): if `X` is an `(n−1)`-connected `G`-CW complex in
which the stabilizer of each `p`-cell is of type `F_{n−p}`, and `X_1 ⊆ X_2 ⊆ ⋯` is a
filtration by `G`-cocompact subcomplexes with union `X`, then `G` is of type `F_n` if and
only if the filtration is essentially `(n−1)`-connected: for every `j` there is `j' ≥ j`
such that every map `S^k → X_j` with `0 ≤ k ≤ n−1` extends to a map `D^{k+1} → X_{j'}`.

Applied to `X = sd Δ(G)`, `X_R = sd VR_R(G)`: `G` is of type `F_n` iff `(VR_R(G))_R` is
essentially `(n−1)`-connected.

## 5. Transfer

Fix `n` finite (for `n = ∞` apply the finite case for every `n`). Suppose `A` is of type
`F_n`. Write `G = A` with `d_S` and `H = A_T` with `d_T`.

- `θ` induces simplicial maps `ι_R : VR_R(H) → VR_R(G)`, since `d_S ≤ d_T` on `H`.
- `r` induces simplicial maps `ρ_R : VR_R(G) → VR_R(H)` (a vertex map sending each simplex to
  a simplex), since `r` is 1-Lipschitz; images of simplices may have fewer vertices, which
  simplicial maps allow.
- `ρ_R ∘ ι_R = id`, because `r ∘ θ = id`; and `ι`, `ρ` commute with the inclusions
  `VR_R ⊆ VR_{R'}`, because they are induced by the same vertex maps for every `R`.

Let `R ≥ 1`. By Section 4 applied to `G`, there is `R' ≥ R` such that every map
`f : S^k → VR_R(G)`, `k ≤ n−1`, extends to `D^{k+1} → VR_{R'}(G)`. Given `g : S^k → VR_R(H)`,
let `F : D^{k+1} → VR_{R'}(G)` extend `ι_R ∘ g`. Then `ρ_{R'} ∘ F : D^{k+1} → VR_{R'}(H)`
restricts on `S^k` to `ρ_{R'} ∘ ι_R ∘ g = ρ_R ∘ ι_R ∘ g = g`. So the Rips filtration of `H`
is essentially `(n−1)`-connected, and by Section 4 applied to `H` (finitely generated by
`T`), `A_T` is of type `F_n`. ∎

**Calibration.** The argument uses nothing but a 1-Lipschitz retraction on vertex sets, so it
cannot say anything about subgroups that are not coarse retracts, such as the kernel of
`F_2 × F_2 → Z` (finitely generated, not finitely presented). For right-angled Artin groups
the conclusion is the known one, obtained there from the algebraic retraction that kills the
generators outside `T`. That map differs from `r`: for `S = {s, x}`, `m_sx = ∞`, `T = {s}`,
the word `σ_x σ_s` has `t_2 = x s x ∉ T`, so `r(σ_x σ_s) = 1`, while killing `σ_x` gives `σ_s`.
Only the Lipschitz and retraction properties are used, and both hold for `r`.

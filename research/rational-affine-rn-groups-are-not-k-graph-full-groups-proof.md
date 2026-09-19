---
rg: 2
id: rational-affine-rn-groups-are-not-k-graph-full-groups-proof
kind: route
title: Odometer averaging kills translation cocycles, density makes the rest a multiplier character; the degree skew product of a k-graph is AF while the multiplier skew product has core Z[1/m] x Z_p with H_1 = Z[1/m]
target: rational-affine-rn-groups-are-not-k-graph-full-groups
requires:
  - dyadic-affine-germ-groupoids-are-not-k-graph-groupoids
  - s-arithmetic-affine-rn-groups-are-k-graph-full-groups
  - basilica-rn-group-is-not-a-k-graph-full-group
  - finite-k-graph-boundary-groupoid-standard-facts
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/one_vertex_digit_search.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-one-vertex-digit-search.txt
---

Notation as in the claim: `R = Z[1/pm]`, `B = Z[1/m] = R ∩ Z_p`, `μ` is Haar probability measure on `Z_p`, and
`[ux + b, ω]` is the germ at `ω`. For a groupoid `H` and a continuous cocycle `c : H → Γ` (Γ discrete abelian), the
**skew product** `H ×_c Γ` has units `(x, n)` and arrows `(γ, n) : (s γ, n) → (r γ, n + c(γ))`.
`∂g(γ) = g(rγ) - g(sγ)`. Homology is Crainic–Moerdijk/Matui homology. It is invariant under isomorphism and under
passing between the reductions of one étale groupoid to two clopen sets that meet every orbit (Morita invariance).

## Three elementary facts about `𝒢`

- **(F1) Density.** `R` and `B` are dense in `Q_p` and `Z_p`, since `m` is prime to `p`.
  - For each `x ∈ Z_p`, each `u ∈ U` and each nonempty open `Y ⊆ Z_p`, some germ `[ux + b, x]` has range in `Y`:
    take `b ∈ R ∩ (Y - ux)`.
- **(F2) Isotropy.** For `β ∈ B`, the germs `[u(x - β) + β, β]`, `u ∈ U`, lie in `𝒢`, since
  `(1 - u)β ∈ R`. They are pairwise distinct, since the multiplier is a germ invariant.
  - So the isotropy of `𝒢` at `β` contains a copy of `U` on which `u` is the identity.
- **(F3) Core.** `[x + b, ω] ∈ 𝒢` iff `b ∈ R ∩ Z_p = B`, and then the germ is defined at every point. So
  `ker u = B ⋉ Z_p`.
  - For `n ≥ 0` put `γ_n = m^{-n} ∈ B`. Then `B = ⋃_n Z γ_n`, with `γ_n = m γ_{n+1}`. Translation by `γ_n`, a
    `p`-adic unit, is conjugate (by `x ↦ γ_n x`) to `x ↦ x + 1`. So it is a minimal, uniquely ergodic odometer
    with invariant measure `μ`.

**Import (odometer dimension group).** For `T x = x + 1` on `Z_p`, the map `f ↦ ∫ f dμ` induces
`C(Z_p, Z)/(f - f∘T) ≅ Z[1/p]`. In particular, an `h ∈ C(Z_p,Z)` with `∫ h dμ = 0` is `f∘T - f` for some `f`.
Transported by the conjugacy, the same holds for translation by any `γ_n`.

## Part 1: cocycle rigidity

Let `ψ : 𝒢 → Z` be a continuous homomorphism.

**Step 1a (the core).** Put `h_n(x) = ψ[x + γ_n, x] ∈ C(Z_p, Z)` and `I_n = ∫ h_n dμ ∈ Z[1/p]`.
- From `[x + γ_n, x] = ∏_{i<m} [x + γ_{n+1}, x + iγ_{n+1}]` we get `h_n = Σ_{i<m} h_{n+1}(· + iγ_{n+1})`.
  Hence `I_n = m I_{n+1}`, since `μ` is translation invariant.
- So `I_0 ∈ ⋂_j m^j Z[1/p] = 0`, because `m > 1` and `gcd(m, p) = 1`. Then `I_n = m^{-n} I_0 = 0` for every `n`.
- By the import, `h_n = g_n(· + γ_n) - g_n` for some `g_n ∈ C(Z_p,Z)`. Normalise `g_n(0) = 0`.
- Then `ψ[x + kγ_n, x] = g_n(x + kγ_n) - g_n(x)` for all `k ∈ Z`, by the cocycle identity.
  - Now `g_{n+1}` also satisfies this for the subgroup `Zγ_n ⊆ Zγ_{n+1}`. So `g_n - g_{n+1}` is invariant under
    translation by `γ_n`.
  - It is continuous, hence constant, by minimality. Both vanish at `0`, so `g_n = g_{n+1} =: g`.
- So `ψ = ∂g` on `ker u = B ⋉ Z_p`. Put `ψ' = ψ - ∂g`. It is a continuous homomorphism vanishing on `ker u`.

**Step 1b (constant on each multiplier class).** Fix `u = p^j u_0 ∈ U`, where `j = v_p(u)` and `u_0 ∈ Z[1/m]^×`.
Let `𝒢_u = u^{-1}(u)`.
- For `c, c' ∈ B`: `[x + c', ·] · [ux + b, ω] · [x + c, ω - c] = [ux + (b + uc + c'), ω - c]`.
  - The outer factors lie in `ker u`, so `ψ'` takes the same value on `[ux + b, ω]` and on
    `[ux + b + uc + c', ω - c]`.
- **All translation parts are equivalent.** A germ `[ux + b, ω]` exists iff `b ∈ R ∩ (Z_p + uZ_p)`. This set is
  `R ∩ p^{min(0,j)} Z_p = p^{min(0,j)} B`.
  - That equals `B + uB = B + p^j B`, since `u_0 B = B`.
  - So every germ in `𝒢_u` can be moved, by the displayed operation, to one with any prescribed admissible `b`.
- **Fixed `b`.** The domain `D_b = {ω : uω + b ∈ Z_p}` is a coset of `p^{max(0,-j)} Z_p` in `Z_p`.
  - `ω ↦ ψ'[ux + b, ω]` is continuous on `D_b`, since `{[ux+b, ω] : ω ∈ D_b}` is an open bisection.
  - It is invariant under `ω ↦ ω - c` for every `c` with `uc + c' = 0` for some `c' ∈ B`, i.e. for every
    `c ∈ B ∩ u^{-1}B = p^{max(0,-j)} B`.
  - This group is dense in `p^{max(0,-j)} Z_p` by (F1). So the function is constant on `D_b`.
- Hence `ψ'` is constant on `𝒢_u`. Call the value `χ(u)`.
- Composable germs with multipliers `u` and `u'` exist, by (F1), and their product has multiplier `uu'`. So
  `χ : U → Z` is a homomorphism.
- **Conclusion.** `ψ = χ ∘ u + ∂g`, and `H^1(𝒢; Z) = Hom(U, Z)`. For injectivity: if `χ ∘ u = ∂g`, evaluate at the
  isotropy of (F2), where `∂g = 0`; this gives `χ = 0`. The same holds with values in `Z^k`, coordinatewise.

## Part 2: `H_1(B ⋉ Z_p) = Z[1/m]`

- Homology of a transformation groupoid is group homology with coefficients in `M = C(Z_p, Z)`.
- Group homology commutes with directed unions, so `H_1(B; M) = lim_n H_1(Zγ_n; M)`.
- For the cyclic group, `H_1(Zγ_n; M) = M^{Zγ_n}`. These are the constants `Z`, by minimality, via `f ↦ [γ_n ⊗ f]`.
- Under the inclusion `Zγ_n → Zγ_{n+1}`, `[γ_n ⊗ 1] = [mγ_{n+1} ⊗ 1] = m[γ_{n+1} ⊗ 1]`, since `1` is invariant.
  So the connecting maps are multiplication by `m`.
- Hence `H_1 = lim(Z →m Z →m ⋯) = Z[1/m] ≠ 0`.
- Its reduction to any nonempty clopen `Y ⊆ Z_p` has the same `H_1`, since `Y` meets every orbit (minimality).

## Part 3: the AF-core obstruction

Suppose `𝒢|_Y ≅ G_Λ|_W` for full clopen sets `Y ⊆ Z_p` and `W ⊆ Λ^∞`, where `Λ` is a finite `k`-graph with no
sources. Let `d : G_Λ → Z^k`, `(λz, d(λ) - d(μ), μz) ↦ d(λ) - d(μ)`, be the degree cocycle, and let `c` be its
transport to `𝒢|_Y`.

**Step 3a (the `k`-graph side is AF up to Kakutani equivalence).**
- `ker d = ⋃_N R_N`, where `R_N = {(λz, 0, μz) : d(λ) = d(μ) = N}`.
  - Each `R_N` is a compact open elementary principal subgroupoid, and `R_N ⊆ R_{N+M}` (extend `λ, μ` by `z(0,M)`).
  - So `ker d` is AF, and `H_1(ker d) = 0` (Matui).
- In `G_Λ ×_d Z^k`, the clopen `Λ^∞ × {0}` meets every orbit.
  - Given `(x, n)`, take `N ≥ n` in `N^k` and put `μ = x(0, N)`, `λ = x(N - n, N)`, `z = σ^N x`. Then
    `s(λ) = x(N) = r(z)`, and `g = (λz, d(λ) - d(μ), μz)` has `s(g) = x` and `d(g) = (N - n) - N = -n`. So `(x, n)`
    is equivalent to `(λz, 0)`. Only paths inside `x` are used, so no hypothesis on sinks is needed.
  - Its reduction is `ker d`.
- `W × Z^k` also meets every orbit, since `W` is full.
- By Morita invariance, `H_1(G_Λ|_W ×_d Z^k) = H_1(ker d) = 0`.
- It is principal. An isotropy arrow `((x, n', x), a)` has `d = n' = 0`, so it is a unit.

**Step 3b (the `𝒢` side).**
- **Extension.** Refine a clopen partition of `Z_p` so that each piece `Z_i` is contained in `Y`, or carries a compact
  open bisection `σ_i` with `s(σ_i) = Z_i`, `r(σ_i) ⊆ Y`. This is possible by fullness and compactness.
  - On pieces inside `Y`, take `σ_i` to be the identity.
  - Then `c̃(γ) = c(σ γ σ^{-1})` (conjugating by the `σ_i` at source and range) is a continuous cocycle on `𝒢` with
    `c̃|_{𝒢|_Y} = c`.
- By Part 1, coordinatewise, `c̃ = χ ∘ u + ∂g` with `χ : U → Z^k` a homomorphism. So `c = χ ∘ u + ∂(g|_Y)` on `𝒢|_Y`.
- **Cohomologous cocycles.** `(x, n) ↦ (x, n + g(x))`, `(γ, n) ↦ (γ, n + g(sγ))` is an isomorphism
  `𝒢|_Y ×_{χu} Z^k ≅ 𝒢|_Y ×_c Z^k`.
  - The right side is `≅ G_Λ|_W ×_d Z^k`: principal, with `H_1 = 0`.
- **`χ` is injective.** Pick `β ∈ B ∩ Y` (F1). By (F2), the arrows `([u(x-β)+β, β], 0)` with `χ(u) = 0` are isotropy
  in `𝒢|_Y ×_{χu} Z^k`. Principality forces `u = 1`.
- **Decomposition.** Put `L = χ(U) ≅ U`. Then `𝒢|_Y ×_{χu} Z^k` is the disjoint union, over the cosets `a + L`, of
  groupoids isomorphic to `𝒢|_Y ×_u U` (write `n = a + χ(v)`).
- In `𝒢|_Y ×_u U`, the clopen `Y × {1}` meets every orbit, by (F1) applied inside `Y`. Its reduction is
  `(ker u)|_Y = (B ⋉ Z_p)|_Y`.
- So `H_1(𝒢|_Y ×_{χu} Z^k) = ⊕_{Z^k/L} Z[1/m] ≠ 0` (Part 2). This contradicts Step 3a. ∎

**Full groups.** Under (H), `G_Λ` is minimal, effective and Hausdorff, and so is `𝒢`. By part 1 of
`basilica-rn-group-is-not-a-k-graph-full-group` (Matui's isomorphism theorem), `V_p(H) ≅ F(G_Λ)` gives `𝒢 ≅ G_Λ`, which
is excluded. For `V_3(BS(1,2))`, take `(p, m, U) = (3, 2, ⟨2, 3⟩)`.

## Calibration

- **`F_q(t)`.** Parts 1 and 3 go through verbatim, with a different conclusion.
  - Step 1a is replaced by: `B` is locally finite, and a finite group acting freely on a Cantor set has
    `H^1 = 0` on `C(X, Z)`.
  - But `B ⋉ F_q[[t]]` is AF, so Part 2 fails and nothing is contradicted. This matches the models of
    `s-arithmetic-affine-rn-groups-are-k-graph-full-groups`, where `d` is literally the multiplier.
- **`m = 1`.** Step 1a breaks: `I_0 ∈ Z[1/p]` survives, and `H^1(Z ⋉ Z_p; Z) = Z[1/p]`. The odometer groupoid is
  excluded by a different argument (rational homology). So the hypothesis `m > 1` is exactly where the method is
  needed.
- **Direct search.** `one_vertex_digit_search.py` looks for one-vertex 2-graphs inside `Aff(Z[1/6], ⟨2,3⟩)` of the
  shape used over `F_q(t)`. It tests 1,346 admissible digit pairs (`d = 1`, widths `≤ 60`; `d = 2`, widths `≤ 6`)
  and finds none, as Part 3 predicts.

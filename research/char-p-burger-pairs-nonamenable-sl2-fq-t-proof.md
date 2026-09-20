---
rg: 2
id: char-p-burger-pairs-nonamenable-sl2-fq-t-proof
kind: route
title: "Almost invariant vectors without M-invariant vectors give a Λ-invariant mean on the dual K²/R² concentrated at 0 minus 0; projectivizing gives an invariant mean on P¹(F_q((1/t))) = boundary of the Bruhat–Tits tree, and the amenable boundary action of the discrete group Λ then makes Λ amenable"
target: char-p-burger-pairs-for-nonamenable-subgroups-of-sl2-fq-t
requires: []
---

Notation as in the target. Put `K = F_q((1/t))` with valuation `v(t) = −1`, and `O = F_q[[1/t]]`, so
`K = R ⊕ t^{-1}O` as `F_q`-spaces. For `λ ∈ SL_2(R)` let `d(λ)` be the largest degree of an entry of
`λ` or of `λ^{-1}`. The argument is written for `Λ ≤ SL_2(R)`. For `Δ ⋉_ρ M`, replace `λ` by
`ρ(δ)` throughout; nothing uses injectivity.

**Step 0 (the dual of M).** Define `⟨x, r⟩ = tr_{F_q/F_p}(res(x^T r)) ∈ F_p` for `x ∈ K²`, `r ∈ R²`.
Here `res` is the coefficient of `t^{-1}`. Put `χ_x(r) = exp(2πi⟨x,r⟩/p)`.
- If `x = Σ a_i t^i`, then `res(x t^j) = a_{-1-j}`. So `x ⊥ R` iff `a_i = 0` for all `i ≤ −1`, that is,
  iff `x ∈ R` (the trace form is nondegenerate). Hence `x ↦ χ_x` identifies `M̂` with `K²/R²`. Every
  character has a unique *canonical representative* `x ∈ (t^{-1}O)²`. (The map is onto `M̂`: a
  character of `R²` is a coefficient sequence, which is exactly an element of `(t^{-1}O)²`.)
- The dual action `(λχ)(r) = χ(λ^{-1}r)` is `λ·χ_x = χ_{λ^{-T}x}`, since
  `res(x^T λ^{-1} r) = res((λ^{-T}x)^T r)`.
- Put `U_N = {χ_x : x ∈ (t^{-N}O)²}` for `N ≥ 1`. A product `x r` with `v(x) ≥ N` and `deg r ≤ j` has
  valuation `≥ N − j`, so has zero residue when `j ≤ N − 2`. Conversely, among canonical
  representatives, killing all `r` of degree `≤ N−2` forces `a_{-1} = … = a_{-(N−1)} = 0`. So `U_N` is
  the annihilator of the finite subgroup `P_N = {r ∈ R² : deg r ≤ N−2}`. The `U_N` form a basis of
  neighbourhoods of `0` and are clopen.
- **Canonical representatives are preserved near 0.** If `χ_x ∈ U_N` with `N ≥ d(λ) + 1` and `x`
  canonical, then `λ^{-T}x` has valuation `≥ N − d(λ) ≥ 1`, so it is the canonical representative of
  `λ·χ_x`. Also `λ U_N ⊇ U_{N + d(λ)}`, because `y = λ^{-T}(λ^T y)` and `λ^T y ∈ (t^{-N}O)²` when
  `v(y) ≥ N + d(λ)`.

**Step 1 (an invariant mean on the dual, off 0).** Suppose `(Γ, M)` fails relative (T). `Γ` is countable,
so there are a unitary representation `(π, V)` with `V^M = 0` and unit vectors `ξ_n` with
`‖π(g)ξ_n − ξ_n‖ < 1/n` for all `g` in a finite set `Q_n`, where `Q_1 ⊂ Q_2 ⊂ …` exhausts `Γ`.
- By the spectral theorem for the countable abelian group `M`, there is a projection-valued measure
  `E` on the Borel sets of the compact group `M̂` with `π(r) = ∫ χ(r) dE(χ)`. Then `E({0})` is the
  projection onto `V^M = 0`.
- For `γ = (λ, 0)`, `π(γ)π(r)π(γ)^{-1} = π(λr)` gives `π(γ)E(B)π(γ)^{-1} = E(λB)`.
- Put `μ_n(B) = ⟨E(B)ξ_n, ξ_n⟩`, a Borel probability on `M̂`. Then:
  - `μ_n({0}) = 0`;
  - `|μ_n(λB) − μ_n(B)| ≤ 2‖π(γ^{-1})ξ_n − ξ_n‖`, since `μ_n(λB) = ⟨E(B)π(γ^{-1})ξ_n, π(γ^{-1})ξ_n⟩`;
  - for `r ∈ M`, `χ(r)` is a `p`-th root of unity, so `|χ(r) − 1| ≥ c_p = |e^{2πi/p} − 1|` when
    `χ(r) ≠ 1`, and `μ_n({χ : χ(r) ≠ 1}) ≤ ‖π(r)ξ_n − ξ_n‖² / c_p²`.
- By the last bullet and a union bound over the finite set `P_N`, `μ_n(U_N) → 1` for every `N`.
- Fix a nonprincipal ultrafilter `𝔲` and put `m(B) = lim_𝔲 μ_n(B)`. Then `m` is a finitely additive
  probability on the Borel sets of `M̂`. It is `Λ`-invariant, `m({0}) = 0`, and `m(U_N) = 1` for all `N`.

**Step 2 (projectivize).** Let `Φ : M̂ ∖ {0} → P¹(K)` send `χ_x`, with `x` canonical and nonzero, to
the line `[x]`. It is Borel (continuous on each clopen piece where a fixed coordinate of `x` has a fixed
leading term). For a Borel `A ⊂ P¹(K)` put `ν(A) = m(Φ^{-1}(A))`. This is a finitely additive
probability, since `m(M̂ ∖ {0}) = 1`.
- Let `Λ' = {λ^{-T} : λ ∈ Λ}`, a group isomorphic to `Λ`, acting on `P¹(K)` projectively.
- **Claim.** `ν(λ^{-T}A) = ν(A)`. Take `N ≥ d(λ) + 1`. By Step 0, for canonical `x ≠ 0` with
  `χ_x ∈ U_N`, the canonical representative of `λχ_x` is `λ^{-T}x`, and `[λ^{-T}x] = λ^{-T}[x]`. So
  `λ(Φ^{-1}(A) ∩ U_N) = Φ^{-1}(λ^{-T}A) ∩ λU_N`.
- Since `m(U_N) = 1` and `m(λU_N) ≥ m(U_{N+d(λ)}) = 1`,
  `ν(λ^{-T}A) = m(Φ^{-1}(λ^{-T}A) ∩ λU_N) = m(λ(Φ^{-1}(A) ∩ U_N)) = m(Φ^{-1}(A) ∩ U_N) = ν(A)`.
- A finitely additive probability integrates bounded Borel functions (uniform limits of simple
  ones), and the invariance gives `∫ F(g^{-1}ω) dν(ω) = ∫ F dν` for bounded Borel `F` and `g ∈ Λ'`.

**Step 3 (the tree; recalled from Serre, *Trees*, Chapter II, §1).** Let `T` be the Bruhat–Tits tree of
`SL_2(K)`: vertices are homothety classes of `O`-lattices in `K²`, and `T` is `(q+1)`-regular.
`SL_2(K)` acts by isometries, vertex stabilizers are compact (conjugates of `SL_2(O)`), and the end
space `∂T` is identified `SL_2(K)`-equivariantly with `P¹(K)`. (The identification is also Borel:
cylinder sets of ends correspond to balls in `P¹(K)`.)
- `Λ' ≤ SL_2(R)` is discrete in `SL_2(K)`, because `R` is discrete in `K` (`R ∩ t^{-1}O = 0`). A
  discrete subgroup meets a compact one in a finite group, so every `Λ'`-stabilizer of a vertex is finite.
- Fix a vertex `v_0`. For `ω ∈ ∂T` let `u_0 = v_0, u_1, u_2, …` be the ray from `v_0` to `ω`, and let
  `η^n_ω` be the uniform probability on `{u_n, …, u_{2n−1}}`.
- **Window estimate.** For `g ∈ Λ'` with `D = d(v_0, g v_0) ≤ n`, the rays from `v_0` and from `g v_0`
  to `gω` coincide after at most `D` steps, with an index shift `s` satisfying `|s| ≤ D`. So `gη^n_ω` and
  `η^n_{gω}` are uniform on two windows of `n` consecutive vertices of one ray, offset by at most `D`.
  Hence `‖gη^n_ω − η^n_{gω}‖_1 ≤ 2D/n`.
- **From vertices to the group.** Choose a representative `v_*` in each `Λ'`-orbit of vertices. For
  a vertex `v` in the orbit of `v_*`, let `β_v` be the uniform probability on the finite coset
  `{h ∈ Λ' : h v_* = v}`. Then `g β_v = β_{gv}` exactly.
- Put `μ^n_ω = Σ_v η^n_ω(v) β_v ∈ Prob(Λ')`. Then `‖g μ^n_ω − μ^n_{gω}‖_1 ≤ 2D/n`. Also
  `μ^n_ω` depends only on `u_1, …, u_{2n−1}`, so `ω ↦ μ^n_ω` is locally constant on `∂T`: it is constant
  on each of finitely many cylinder sets. Hence `ω ↦ μ^n_ω(f)` is a bounded Borel function for every
  `f ∈ ℓ^∞(Λ')`.

**Step 4 (Λ is amenable, contradiction).** Let `g` act on `ℓ^∞(Λ')` by `(g f)(h) = f(g^{-1}h)`, so
that `μ(g f) = (g^{-1}μ)(f)`. Put `M_n(f) = ∫ μ^n_ω(f) dν(ω)`, a mean on `ℓ^∞(Λ')`. Let `n ≥ D`,
with `D = d(v_0, g^{-1}v_0)`.
- By Step 3, `|μ^n_ω(g f) − μ^n_{g^{-1}ω}(f)| ≤ 2D‖f‖_∞/n`.
- By the invariance of `ν` from Step 2, `∫ μ^n_{g^{-1}ω}(f) dν(ω) = M_n(f)`.
- So `|M_n(g f) − M_n(f)| ≤ 2D‖f‖_∞/n`, and `M = lim_𝔲 M_n` is a `Λ'`-invariant mean on `ℓ^∞(Λ')`.

So `Λ ≅ Λ'` is amenable. This contradicts non-amenability, and proves that non-amenable `Λ` gives
relative (T). In the `ρ` version, the same steps show that `ρ(Δ)` is amenable.

**Step 5 (converse and free subgroups).**
- If `Λ` is amenable, then `Γ = Λ ⋉ M` is amenable, being an extension of an amenable group by an
  abelian one. So `ℓ²(Γ)` has almost invariant vectors. It has no nonzero `M`-invariant vector, because
  `M` is infinite. So relative (T) fails.
- `SL_2(F_q[t])` is non-amenable, by either of two recalled facts:
  - it is a lattice in the non-amenable group `SL_2(K)`;
  - Nagao's theorem writes it as the amalgam `SL_2(F_q) *_{B(F_q)} B(F_q[t])`, with indices `q + 1 ≥ 3`
    and `∞`, and such an amalgam contains `F_2`.
- For the Tits route: amenability is local, so some finitely generated subgroup is non-amenable. By
  the Tits alternative for finitely generated linear groups in any characteristic, that subgroup is
  virtually solvable, and hence amenable, unless it contains `F_2`. So it contains `F_2`.
- Every `F_2 ≤ SL_2(F_q[t])` is non-amenable, so Step 4 applies to `F_2 ⋉ F_q[t]²`. This gives item 3.

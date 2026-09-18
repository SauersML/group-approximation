---
rg: 2
id: brothier-problem-b-value-range-domination-proof
kind: route
title: Pull Farley's function back through every congruence quotient C(C,Γ/Γ_N) ⋊ V ≤ V, glue with summable weights, and add the value-range function
target: brothier-problem-b-reduces-to-value-range-domination
requires:
  - twisted-power-cloning-groups-embed-in-v
  - thompson-v-has-haagerup-property
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Notation as in the target. All cnd functions vanish at `e` and are symmetric. For a cnd
`ψ` there is an affine isometric action with cocycle `b` and `ψ(g) = ‖b(g)‖²`, so
`√ψ(gh) ≤ √ψ(g) + √ψ(h)`.

**Step 0 (1 ⇒ 2).** If `ψ` is proper on `G_Γ`, then `{f ∈ A_Γ : ψ(f) ≤ R}` is finite,
and a finite union of the finite sets `ran(f)` is finite.

**Step 1 (congruence quotients).**
- `Γ` is countable and residually finite. Enumerate `Γ \ {e} = {γ_1, γ_2, …}` and pick
  finite-index normal `M_k` with `γ_k ∉ M_k`. Put `Γ_N = M_1 ∩ … ∩ M_N`: finite-index,
  normal, decreasing, `γ_k ∉ Γ_N` for `N ≥ k`.
- `Q_N = Γ/Γ_N` is finite, with projection `π_N`. The map
  `q_N(f,h) = (π_N∘f, h)` is a homomorphism `G_Γ → G_{Q_N}`, because
  `π_N∘(f·(h·f')) = (π_N∘f)·(h·(π_N∘f'))`.

**Step 2 (Farley on each quotient).**
- By `twisted-power-cloning-groups-embed-in-v` (part 2, `φ0 = φ1 = id`) the group
  `𝒱_(Q_N,id,id)` embeds in `V`. It is `C(C,Q_N) ⋊ V`: send the class of
  `{(a_i,b_i,k_i)}` to `(f,h)` with `h(b_i w) = a_i w` and `f ≡ k_i` on `[a_i]`.
  - Refinement `(a,b,k) ~ (a0,b0,k),(a1,b1,k)` does not change `(f,h)`.
  - Every `(f,h)` arises: take a table of `h` whose range cylinders refine the
    partition of `f`.
  - Products match: `(f,h)(f',h')` with `h': [c_i] → [b_i]`, `f' ≡ k'_i` on `[b_i]`
    gives `h·f' ≡ k'_i` on `[a_i]`, so `f·(h·f') ≡ k_i k'_i` on `[a_i]` and
    `hh': [c_i] → [a_i]`, which is `{(a_i,c_i,k_i k'_i)}`.
  This is also the artifact's Remark (finite Γ). Call the embedding `ι_N`.
- Let `φ` be Farley's proper cnd function on `V` (`thompson-v-has-haagerup-property`).
  Then `ψ_N = φ∘ι_N∘q_N` is cnd on `G_Γ`, and for every `T` the set
  `{g ∈ G_{Q_N} : φ(ι_N g) ≤ T}` is finite.

**Step 3 (gluing).** Enumerate `G_Γ = {g_1, g_2, …}` and set
`w_N = 2^{-N} / (1 + max_{i ≤ N} ψ_N(g_i))` and `ψ_Σ = Σ_N w_N ψ_N`. For `g = g_i`
every term with `N ≥ i` is at most `2^{-N}`, so the series converges everywhere. Its
partial sums are cnd, hence so is the pointwise limit `ψ_Σ`.

**Step 4 (2 ⇒ proper on A).** Let `ψ_0` be as in condition 2, `p: G_Γ → V` the
projection, and `Ψ = ψ_0 + ψ_Σ + φ∘p`, a cnd function. Fix `R` and let
`S = {f ∈ A_Γ : Ψ(f) ≤ R}`.
- `ψ_0 ≤ Ψ`, so `ran(f) ⊆ E` for all `f ∈ S`, with `E` finite by condition 2.
- `E^{-1}E \ {e}` is finite, so some `N` has `Γ_N ∩ E^{-1}E = {e}`. Then `π_N` is
  injective on `E`, and `q_N` is injective on `{f : ran(f) ⊆ E}`: if `f(x) ≠ f'(x)`
  then `π_N f(x) ≠ π_N f'(x)`.
- On `S`, `ψ_N(f) ≤ R / w_N`, so `q_N(S)` lies in the finite set of Step 2 with
  `T = R/w_N`. Injectivity gives `S` finite.

**Step 5 (proper on G).** Let `Ψ(g) ≤ R`. Then `φ(p(g)) ≤ R`, so `h = p(g)` lies in a
finite set `H_R ⊆ V`. Write `g = (f,h)`, so `(f,1) = g·(1,h)^{-1}` and
`√Ψ(f,1) ≤ √R + max_{h ∈ H_R} √Ψ(1,h)`. By Step 4 only finitely many `f` occur. So
`Ψ` is proper and `G_Γ` has the Haagerup property. ∎

**Remarks.**
- No hypothesis on `Γ` beyond residual finiteness and countability is used, and
  condition 2 forces `Γ` itself to be a-T-menable (restrict `Ψ` to the constants).
- Step 5 is the artifact's §3(d); it is repeated so the route is self-contained.
- For `Γ = Z` take `Γ_N = N!·Z`; condition 2 becomes: `ψ_0(f) ≥ F(‖f‖_∞)` for some
  `F → ∞` (set `F(m) = inf{ψ_0(f) : ‖f‖_∞ ≥ m}`; condition 2 says exactly that `F`
  is unbounded, and `F` is nondecreasing).

---
rg: 2
id: ramsey-functions-are-pairwise-reiter-radii-proof
kind: route
title: Convexify the pairs of window elements, apply the minimax theorem twice, and read off the maximal test function as the positive part of a signed measure
target: ramsey-functions-are-pairwise-reiter-radii
requires: []
---

Notation is as in the claim. Every set below is a finite-dimensional compact convex set, and every payoff is
continuous. So each minimum and maximum is attained, and von Neumann's minimax theorem applies. This covers a payoff
bilinear on a product of two simplices or boxes, and (Sion) a payoff convex in one variable and linear in the other.

**Step 1 (points to pairs of measures).** Fix `m, n, ε, l` and put `N = N_{m,n}`, `Φ = ([0,1]^{B_n})^l` and
`Θ = P({1,…,l} × B_m × B_m)`. For `f ∈ Φ`, `ν ∈ N` and `θ ∈ Θ`, put

`L(ν, θ, f) = Σ_{i,g,g′} θ(i, g, g′) (gν(f_i) − g′ν(f_i))`.

- The index set contains `(i, g′, g)` along with `(i, g, g′)`. So `max_{i,g,g′} |gν(f_i) − g′ν(f_i)| = max_θ L(ν, θ, f)`.
- By definition, `R̃(m, ε, l) ≤ n` iff for every `f ∈ Φ`, `min_{ν∈N} max_θ L < ε`.
- `L` is bilinear in `(ν, θ)`, so by minimax `min_ν max_θ L = max_θ min_ν L`.
- Hence `R̃(m, ε, l) ≤ n` iff `min_ν L(ν, θ, f) < ε` for all `θ` and all `f`.

**Step 2 (remove the test functions).** Fix `θ`. The map `f ↦ min_ν L(ν, θ, f)` is continuous on the compact set `Φ`,
so "for all `f`, `< ε`" is the same as `max_f min_ν L < ε`. `L` is bilinear in `(ν, f)`, so by minimax again this
equals `min_ν max_f L`. For fixed `θ` and `ν`,

`L = Σ_i ⟨σ_i, f_i⟩`, where `σ_i = Σ_{g,g′} θ(i, g, g′)(gν − g′ν)`.

Each `gν` lies in `P(B_n)` because `ν ∈ N`. So `σ_i` is a signed measure on `B_n` of total mass 0. The maximum of
`⟨σ_i, f_i⟩` over `f_i ∈ [0,1]^{B_n}` is attained at the indicator of `{σ_i > 0}`, and it equals `σ_i^+(B_n) = ‖σ_i‖₁/2`.
Hence `R̃(m, ε, l) ≤ n` iff every `θ` has some `ν ∈ N` with `Σ_i ‖σ_i‖₁ < 2ε`.

**Step 3 (reparametrize θ).** Let `w_i` be the mass of `θ` on `{i} × B_m × B_m`. When `w_i > 0`, let `α_i, β_i` be the
two marginals of `θ(i,·,·)/w_i`. By linearity, `σ_i = w_i(α_iν − β_iν)`. Conversely, every choice of `(w, α_i, β_i)`
arises from `θ = Σ_i w_i δ_i ⊗ α_i ⊗ β_i`. This proves (A). The case `l = 1` is `R̃(m, ε) = PR_{2ε}(m)`.

**Step 4 (B).**
- *Upper half.* For sets `E ⊆ B_n`, `1_E ∈ [0,1]^{B_n}`, and `< 1/2` implies `≤ 1/2`. So `R(m) ≤ R̃(m, 1/2) = PR_1(m)`.
- *Lower half.* Let `n = R(m)`, so `B_n` is 1/2-Ramsey with respect to `B_m`. Moore's proof of (2⇒3) in
  Theorem 2.1, quoted in `moore-ramsey-criterion-for-amenability`, gives the following for every `f : B_n → [0,1]`:
  some `ν ∈ N_{m,n}` has `|gν(f) − g′ν(f)| ≤ 3/4` for all `g, g′ ∈ B_m`. For `c > 3/2` this is `< c/2`. So
  `R̃(m, c/2) ≤ n`, that is, `PR_c(m) ≤ R(m)`.
- *Self-contained re-proof of that step.* Moore, arXiv:1106.3127, writes verbatim: "It suffices to prove that B
  satisfies the conclusion of (3) with q = 3/4". Put `E = {b ∈ B_n : f(b) ≥ 1/2}` and take a Ramsey `ν ∈ N_{m,n}` with
  `|gν(E) − g′ν(E)| ≤ 1/2`. The function `f − 1_E/2` takes values in `[0, 1/2]`, so its two evaluations differ by at
  most `1/2`. Hence `|gν(f) − g′ν(f)| ≤ (1/2)(1/2) + 1/2 = 3/4`.

**Step 5 (C).** Fix `r`. The map `ν ↦ max_g ‖gν − ν‖₁` equals `max_{w ∈ P(B_M)} Σ_g w_g ‖gν − ν‖₁`. The payoff is
convex in `ν ∈ P(B_r)` and linear in `w`, so by minimax `min_ν max_w = max_w min_ν`. Hence `CR(M) ≤ r` iff every
`w` has some `ν ∈ P(B_r)` with `Σ_g w_g ‖gν − ν‖₁ ≤ 1`.

**Step 6 (D).** Since `I_{m,9m} ⊇ B_{8m}`, it is enough to find `ν` supported in `B_{8m}`.
- *Point mass.* Let `β = δ_b` and `γ = b⁻¹α ∈ P(B_{2m})`, and put `ν = (δ_e + γ + γ²)/3`, which is supported in
  `B_{4m}`. Then `αν − βν = b(γν − ν) = b(γ³ − δ_e)/3`, of norm at most `2/3 < 1`. The norm is symmetric in `α` and
  `β`, so a point mass `α` is covered as well.
- *Commuting pair.* Let `k = 5`, `A = Σ_{i<k} α^i` and `B = Σ_{j<k} β^j`, and put `ν = AB/k²`, which is supported in
  `B_{8m}`. We have `αA = A − δ_e + α^k` and `βB = B − δ_e + β^k`, and `β` commutes with `A`. Hence
  `k²(αν − βν) = αAB − AβB = (α^k − δ_e)B − A(β^k − δ_e)`. Its norm is at most `2k + 2k`, so
  `‖αν − βν‖₁ ≤ 4/k = 4/5 < 1`.

**Step 7 (E).** Let `E ⊆ F_2` be the set of reduced words whose first letter is `a` or `b`. Put
`h(x) = (1_E(ax) + 1_E(bx) − 1_E(a⁻¹x) − 1_E(b⁻¹x))/2`, which is `(α−β)⋆1_E` in the convention `gν(f) = Σ ν(x) f(gx)`.
We check `h ≥ 1/2` case by case.
- `x = e`: the four values are `1, 1, 0, 0`, so `h = 1`.
- `x` starts with `a`: `ax, bx ∈ E` and `b⁻¹x ∉ E`, so `h = 1 − 1_E(a⁻¹x)/2 ≥ 1/2`.
- `x` starts with `a⁻¹`: `bx ∈ E` and `a⁻¹x, b⁻¹x ∉ E`, so `h = (1_E(ax) + 1)/2 ≥ 1/2`.
- `x` starts with `b` or `b⁻¹`: the same, with `a` and `b` exchanged.

So for every finitely supported `ν`, `(αν − βν)(E) = Σ_x ν(x) h(x) ≥ 1/2`. Hence `‖αν − βν‖₁ ≥ 2 · 1/2 = 1`, and
`PR_1(1) = ∞`. Also `R̃(1, 1/2) = ∞`, because the average of `gν(1_E) − g′ν(1_E)` under `α ⊗ β` is at least 1/2, so
some pair of window elements reaches 1/2.

**Step 8 (Corollary).** Let `c > 3/2`. By (B), `PR_c ≤ R ≤ PR_1` pointwise, and `exp_E` is monotone. So
`exp_E(PR_c(exp_E N)) ≤ exp_E(R(exp_E N)) ≤ exp_E(PR_1(exp_E N))`, and the two implications follow at once. ∎

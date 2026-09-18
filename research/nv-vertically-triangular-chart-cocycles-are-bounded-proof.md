---
rg: 2
id: nv-vertically-triangular-chart-cocycles-are-bounded-proof
kind: route
title: "Codimension-one sweep plus the paradoxical spectral gap of V on chart rows"
target: nv-vertically-triangular-chart-cocycles-are-bounded
requires: []
---

Notation as in the target. Norms of vectors in `H` are written `|·|`. The proof is
self-contained.

**Step 0 (rows).** For a map `p: C^n → C`, put `X_p = {φ ∈ X : pr_n∘φ = p}`. The sets
`X_p` partition `X`. Each is `V × id`-invariant, because `pr_n∘(h × id)∘φ = pr_n∘φ`.
Whether `φ` is vertically triangular depends only on `p`, so `Y` is a union of rows. Put
`v_p = v|_{X_p}`. Since `X_p` is `g_i`-invariant, `(g_i·v)|_{X_p} = g_i·v_p` and
`b(g_i)|_{X_p} = v_p − g_i·v_p`.

**Step 1 (codimension-one sweep: `v_p ∈ ℓ²`).** If `p` is not triangular, then `v_p = 0`.
Otherwise `p(x, y) = w(x)·y`. Fix `x_0` and put `w = w(x_0)`. Let `φ ∈ X_p`. Then
`pr_n∘σ_w∘φ(x_0, y) = s_w(w·y) = w·s(y)`, where `s` swaps the first letter.

We claim `σ_w∘φ ∉ Y`. If it were in `Y`, then some word `w'` would satisfy `w·s(y) = w'·y`
for all `y`. Take `y = 0t`, so `w1t = w'0t` for all `t`.
- If `|w'| = |w|`, the letters at position `|w|+1` differ (1 against 0).
- If `w' = w1u`, then `t = u0t` for all `t`, which is false for `t = 1^ω`.
- If `w = w'0u` with `u` nonempty or empty, then `u1t = t` for all `t`, which is false for
  `t = 0^ω`.

Moreover `σ_w^{-1} = σ_w`. So for `φ ∈ X_p`, `v(σ_w^{-1}φ) = 0`, hence `b(σ_w)(φ) = v(φ)`.
Therefore `‖v_p‖² ≤ ‖b(σ_w)‖² < ∞`. The bound depends on `p` through `w`. Only
finiteness is used below.

**Step 2 (equivariant extraction).** Let `λ` be the Haar probability on `C^n`, and put
`m(φ) = (pr_1∘φ)_*λ ∈ Prob(C)`. For `h ∈ V` we have `m((h × id)·φ) = h_* m(φ)`. For
`r ∈ ℓ²(X_p; H)` with `‖r‖ = 1`, put `μ_r = Σ_φ |r(φ)|² m(φ)`, a probability measure. Since
`|(g·r)(φ)| = |r(g^{-1}φ)|` for `g = h × id`, reindexing gives `h_*μ_r = μ_{g·r}`.

For every Borel set `B ⊆ C`, using `||a|² − |c|²| ≤ |a − c|(|a| + |c|)` and Cauchy–Schwarz:

`|h_*μ_r(B) − μ_r(B)| ≤ Σ_φ ||(g·r)(φ)|² − |r(φ)|²| ≤ ‖g·r − r‖ (‖g·r‖ + ‖r‖) = 2‖g·r − r‖`.

**Step 3 (paradoxical gap).** Let `ν = μ_r`, and let `δ` be the largest value of
`|h_{i*}ν(B) − ν(B)|` over `i` and `B`.
- `h_1^{-1}[00] = [0]`, so `|ν[0] − ν[00]| ≤ δ`, that is `ν[01] ≤ δ`.
- `h_2^{-1}[01] = [0]`, so `ν[00] ≤ δ`. Hence `ν[0] ≤ 2δ`.
- `h_3^{-1}[1] = [0]`, so `ν[1] ≤ ν[0] + δ ≤ 3δ`.

Hence `1 = ν(C) ≤ 5δ`, and by Step 2, `max_i ‖g_i·r − r‖ ≥ 1/10`. By homogeneity, every
`r ∈ ℓ²(X_p; H)` satisfies `Σ_i ‖g_i·r − r‖² ≥ ‖r‖²/100`.

**Step 4 (sum over rows).** By Step 1, `v_p ∈ ℓ²(X_p; H)`. Steps 0 and 3 give
`‖v_p‖² ≤ 100 Σ_i ‖b(g_i)|_{X_p}‖²`. Summing over the disjoint rows gives
`‖v‖² ≤ 100 Σ_i ‖b(g_i)‖²`. So `v ∈ ℓ²(X; H)`, and `b(g) = v − g·v` has norm at most `2‖v‖`
for every `g ∈ nV`.

**Corollary.** With `v(φ) = Σ_k √w_k 1_{A_k}(φ) e_k` and trivial `π`, we get
`|v − g·v|²(φ) = Σ_k w_k 1_{gA_k Δ A_k}(φ)`, so `‖b(g)‖² = ψ(g)`. The theorem gives
`Σ_k w_k|A_k| = ‖v‖² ≤ 100 Σ_i ψ(g_i)`, and `ψ(g) ≤ 4‖v‖²`. ∎

**Where the class dies.** Step 1 forces row-wise ℓ²-summability, because a single swap in
the vertical tree at the depth of the row's prefix pushes the entire row out of the support.
Step 3 then bounds each row uniformly by three elements of `V × id`, because `V` has a
spectral gap on ℓ² of any `V`-set with an equivariant extraction to `Prob(C)`. This is the
same invariant as in `extractable-character-spectra-carry-no-almost-invariant-vectors`.

**Checks of scope.**
- The argument never uses that `b` is finite on the baker's map or on `id × V` beyond `σ_w`.
- The argument is unchanged if the vertical coordinate is any coordinate `j ≠ 1`.
- The argument is unchanged if the extraction uses any coordinate other than `j`.

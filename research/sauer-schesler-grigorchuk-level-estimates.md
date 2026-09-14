---
rg: 2
id: sauer-schesler-grigorchuk-level-estimates
kind: claim
title: Sauer–Schesler level estimates for the truncated Grigorchuk group (small balls, inverted orbits, separation, connected linking graph)
---

**ESTABLISHED (literature import).** Notation, with right actions:
- `𝒢` is the first Grigorchuk group with `S = {a,b,c,d}`, acting on the levels `X_n = {0,1}^n`.
- `𝒢_n ≤ Sym(X_n)` is its image, with truncated generators `S_n` (involutions), and `Γ_n` is the Schreier graph on `X_n`.
- `ρ_n = 1^n`, `η_n = 1^(n−1)0`, `θ_n = ρ_n a_n = 01^(n−1)` and `r_n = 2^⌊n/2⌋`.
- The inverted orbit of a word `w = s_1⋯s_ℓ` at `ω` is `{ω, ωs_ℓ, ωs_(ℓ−1)s_ℓ, …, ωs_1⋯s_ℓ}`.

Then:
1. `γ_𝒢^S(n) ≤ exp(C n^γ)` with `1/2 < γ < 1` (Grigorchuk 1984).
2. For all large `n`, `ξ ∈ {ρ_n, η_n}` and `k ≤ r_n`, inverted orbits of words of length `≤ k` at `ξ` have at most `C k^α` points, and there are at most `exp(C k^α)` of them, with `0 < α < 1`.
3. `d_(Γ_n)(ρ_n, η_n) ≥ 2^(n−3)` for `n ≥ 4`.
4. The graph on `X_n` whose edges are the `𝒢_n`-translates of `{θ_n, ρ_n}` is `K_(2^(n−1),2^(n−1))`, so it is connected.
5. `𝒢_n` acts transitively on `X_n`.

Route: `sauer-schesler-grigorchuk-level-estimates-citation`. Consumer: `el-small-ball-generating-sets-from-grigorchuk-levels`.

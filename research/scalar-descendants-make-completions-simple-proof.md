---
rg: 2
id: scalar-descendants-make-completions-simple-proof
kind: route
title: Saturated ideals contain all descendants, and a scalar entry persists along every diagonal continuation, which no off-degree element commuting with the core can allow
target: scalar-descendants-make-completions-simple
requires:
  - leavitt-nekrashevych-completion-simplicity-criterion
---

Lane proof (bh-algebra, 2026-09-18). Notation as in the claim. `O_k` is the degree-`k` part of `O_ψ(A)`
and `C = O_0` the core.

## 1. Minimality
If `I` is ψ-saturated, then `a ∈ I` gives `ψ(a) ∈ M_d(I)`, and by induction `ψ_j(a) ∈ M_(d^j)(I)`. So a
nonzero saturated `I` contains a nonzero scalar, and `I = A`.

## 2. Two facts about scalars
- `ψ(λ) = λ I_d` for `λ ∈ K`, since `ψ` is unital and `K`-linear. So if `ψ_j(a)_(uu') = λ`, then
  `ψ_(j+m)(a)_(ur, u'r) = λ` for every word `r` of every length `m`.
- The criterion's normal form (part 1): for `y ∈ O_k` and large `L`, `y = Σ s_μ Y_(μν) t_ν` over
  `|μ| − |ν| = k`, `min(|μ|,|ν|) = L`, with unique coefficients `Y_(μν) ∈ A`. Padding uses
  `a = Σ_(|u|=|u'|=j) s_u ψ_j(a)_(uu') t_(u')`.

## 3. Aperiodicity, k > 0
Let `y ∈ O_k` commute with `C`.
- **Shape.** Commuting with the matrix units `s_α t_β` (`|α| = |β| = L`) and comparing unique
  coefficients gives `Y_(μν) = 0` unless `μ = νω`, and `Y_(νω, ν) = w_ω` independent of `ν`:
  - `s_α t_β y` has coefficients `Y_(βμ'', ν)` at `(αμ'', ν)`;
  - `y s_α t_β` has coefficients `Y_(μα)` at `(μ, β)`.
  So `y = Σ_(|ν|=L, |ω|=k) s_(νω) w_ω t_ν`. This uses no hypothesis on `ψ`.
- **Level `L + j`.** Padding gives `y = Σ s_(νωu) ψ_j(w_ω)_(uu') t_(νu')`, with distinct index pairs.
  The same shape at level `L + j` forces `ψ_j(w_ω)_(uu') = 0` unless `ωu = u'ω'` for some `|ω'| = k`.
- **No scalar entries.** Suppose `ψ_j(w_ω)_(uu') = λ ≠ 0`. By §2, for every letter `r`,
  `ωur = u'rω''` for some `ω''`. Comparing the first `j` letters, `u'` is the length-`j` prefix of `ωu`.
  Let `z` be the remaining suffix of length `k >= 1`. Then `zr = rω''`, so the first letter of `z` is `r`.
  Taking two distinct letters `r` (possible since `d >= 2`) is a contradiction.
- So `w_ω` has no scalar descendant, hence `w_ω = 0` by hypothesis, and `y = 0`.

## 4. Aperiodicity, k < 0
Symmetrically, commuting with matrix units gives `y = Σ_(|μ|=L, |ω|=k) s_μ w_ω t_(μω)`:
- `s_α t_β y` has coefficients `Y_(βν)` at `(α, ν)`;
- `y s_α t_β` has coefficients `Y_(μ, αν'')` at `(μ, βν'')`, using `t_(βν'') = t_(ν'') t_β`.
Padding forces `ψ_j(w_ω)_(uu') = 0` unless `ωu' = uω'`. A scalar entry would persist at `(ur, u'r)`, giving
`ωu'r = urω''` for every letter `r`, and the same prefix argument gives a contradiction. So `w_ω = 0` and
`y = 0`.

## 5. Refinement
For a combination `e` of words of positive length, `ψ(e)_(pp) = 0` by hypothesis, and `ψ(c)_(pp) = c`.
So `ψ(c + e)_(pp) = c`. ∎

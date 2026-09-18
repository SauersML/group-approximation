---
rg: 2
id: harmonic-cuntz-ring-is-purely-infinite-simple-proof
kind: route
title: Compress by Cuntz words onto a cylinder where the harmonic coefficient is a nonzero constant
target: harmonic-cuntz-ring-is-purely-infinite-simple
requires: []
---

Notation as in the claim. For a word `α = a_1 ... a_n` put `s_α = s_(a_1) ⋯ s_(a_n)`
and `t_α = t_(a_n) ⋯ t_(a_1)`. Then `(s_α u)(w) = [w ∈ [α]] u(σ^n w)` and
`(t_α u)(w) = u(αw)`. For `f: X -> Q` put `f_α(z) = f(αz)`.

## Operator identities (checked pointwise on `F`)

- **(W1)** `t_β s_α` is `s_(α')` if `α = βα'`, `t_(β')` if `β = αβ'`, and `0` if
  `α, β` are incomparable. Also `s_α s_γ = s_(αγ)` and `t_γ t_α = t_(αγ)`.
- **(W2)** `m_f s_α = s_α m_(f_α)` and `t_α m_f = m_(f_α) t_α`.
- **(W3)** `m_f = Σ_(|γ| = L) s_γ m_(f_γ) t_γ` for every `L`. Hence
  `s_μ m_f t_ν = Σ_(|γ|=L) s_(μγ) m_(f_γ) t_(νγ)` (**lengthening**).
- **(W4)** For words `δ, τ` with `τ` nonempty, `t_(τδ) s_δ ≠ 0` iff `δ` is a prefix
  of `τδ`, iff `δ` is a prefix of `τ^∞`. The second equivalence is by induction on
  `|δ|`: if `|δ| > |τ|` and `δ` is a prefix of `τδ`, then `δ = τδ''` with `δ''` a
  prefix of `τδ''`.

## The algebra 𝒜 and the span S

Let `𝒬` be the rational functions in `Q(t)` with no pole in `N` and a finite limit at
`∞`; it is a Q-algebra, closed under `r(t) ↦ r(t+1)`, and contains `1/(1+t)` and
`(1+t)/(2+t)`.
- **Refinement.** Since `k(0z) = 0` and `k(1z) = 1 + k(z)`, level-`n` data
  `(r_γ)` of `f ∈ 𝒜` give level-`n+1` data `r_(γ0) = r_γ(0)` and
  `r_(γ1)(t) = r_γ(t+1)`, which lie in `𝒬`.
- **Closure.** So `𝒜` is a unital Q-algebra, computed levelwise. It contains `η`,
  `ζ` (level 0) and every cylinder indicator. It is closed under `f ↦ f_α` and under
  `f ↦ f^α`, where `f^α(w) = [w ∈ [α]] f(σ^(|α|) w)`.
- **(A5) Nonvanishing.** If `0 ≠ f ∈ 𝒜` then some `r_γ ≠ 0` in `𝒬`: if all `r_γ = 0`,
  then also `r_γ(∞) = 0`, so `f = 0`. A nonzero rational function has finitely many
  zeros, so `r_γ(j) ≠ 0` for some `j ∈ N`. With `δ = γ 1^j 0` this gives
  `f_δ ≡ r_γ(j) =: λ ∈ Q^x`.
- **(A6) Aperiodic points decide.** If `f ∈ 𝒜` vanishes at every point that is not
  eventually periodic, then `f = 0`. Indeed `z = 1^j 0 z'` with `z'` not eventually
  periodic is not eventually periodic and has `k(z) = j`, so `r_γ(j) = 0` for all `j`.

Let `S` be the Q-span of the operators `s_α m_f t_β` with `f ∈ 𝒜`. By (W1)–(W2),
`(s_α m_f t_β)(s_γ m_g t_δ)` is `s_(αγ') m_(f_(γ') g) t_δ` if `γ = βγ'`, is
`s_α m_(f g_(β')) t_(δβ')` if `β = γβ'`, and is `0` otherwise. So `S` is a unital
subring of `End_Q(F)` containing the six generators, and `C_h ⊆ S`. This is part 2.
Every computation below takes place in `S`. The division witnesses produced are
words in the generators times rationals, so they lie in `C_h`.

**Part 1.** By the formulas, `t_0 t_1^k m_η s_1^k s_0` sends `u` to
`w ↦ η(1^k 0 w) u(w) = u(w)/(k+1)`.

## Independence and grading

- **(C3)** If `Σ_(μ ∈ M) s_μ m_(g_μ) = 0` with `M` a finite set of distinct words and
  `g_μ ∈ 𝒜`, then every `g_μ = 0`.
  - Take `w` not eventually periodic. Its shifts `σ^j w` are then pairwise distinct.
  - For a prefix `μ ∈ M` of `w`, apply the operator to the indicator of the point
    `σ^(|μ|) w` and evaluate at `w`. Distinct prefixes have distinct lengths, so
    only the `μ` term survives, and `g_μ(σ^(|μ|) w) = 0`.
  - So `g_μ` vanishes at all points that are not eventually periodic, and `g_μ = 0`
    by (A6).
- **Grading.** Give `s_α m_f t_β` degree `|α| - |β|`. By the product formulas the
  degrees add. The sum `S = ⊕_d S_d` is direct:
  - if `Σ_d a_d = 0`, lengthen every term so that all right words have one length
    `L`;
  - for each `|β| = L`, `Σ_d a_d s_β` is a combination `Σ s_μ m_(g_μ)` with
    `|μ| = d + L`, so the words differ across degrees;
  - (C3) kills each `a_d s_β`, and `a_d = Σ_β a_d s_β t_β = 0`.

## Part 3: two-sided division

Let `0 ≠ a ∈ C_h`. Write `a = Σ_i s_(μ_i) m_(f_i) t_(ν_i)` and lengthen so that
every `|ν_i| = L`.
1. **Pick a right word.** Since `a = Σ_(|β|=L) a s_β t_β`, some `b := a s_β` is
   nonzero, and `b = Σ_(μ ∈ M) s_μ m_(g_μ)` with distinct words `μ` and nonzero
   `g_μ ∈ 𝒜`.
2. **Cut at a longest word.** Let `μ*` be of maximal length in `M`. By (W1),
   `c := t_(μ*) b = m_(g_0) + Σ_(j) t_(τ_j) m_(h_j)`, where:
   - `g_0 = g_(μ*) ≠ 0`;
   - `τ_j` ranges over the nonempty words with `μ* = μ τ_j` for `μ ∈ M`;
   - `h_j ∈ 𝒜`.
3. **Choose a cylinder.** By (A5) there are `δ_0` and `λ ∈ Q^x` with
   `(g_0)_(δ_0) ≡ λ`.
   - Extend `δ = δ_0 ε` with `|ε| = e`, where `2^e` exceeds the number of `j`. At most
     one word of each length is a prefix of `τ_j^∞`, so some `ε` makes `δ` a prefix
     of no `τ_j^∞`.
   - Still `(g_0)_δ ≡ λ`.
4. **Compute.** By (W2) and (W1), `t_δ c s_δ = m_((g_0)_δ) + Σ_j t_(τ_j δ) s_δ m_((h_j)_δ)`.
   Every `t_(τ_j δ) s_δ` is `0` by (W4). So `t_δ c s_δ = λ`.

Hence `(λ^(-1) t_δ t_(μ*)) · a · (s_β s_δ) = 1`, with both factors in `C_h`. A ring
with two-sided division and `1 ≠ 0` is simple.

## Part 4: centre

Let `z` be central in `C_h`, with components `z = Σ_d z_d`, `z_d ∈ S_d`.
- **Components are central.** For a homogeneous generator `x` of degree `e`, the
  elements `z_d x` and `x z_d` lie in `S_(d+e)`. So `z x = x z` gives `z_d x = x z_d`
  by directness. Each `z_d` therefore commutes with `C_h`.
- **d ≠ 0 vanishes.**
  - Since `z_d` commutes with `s_γ`, `z_d = t_γ z_d s_γ` for every word `γ`.
  - For `|γ| >` all word lengths in `z_d`, a term `s_μ m_f t_ν` contributes
    `t_(γ') s_(γ'') m_(f_(γ''))`, where `γ = μγ' = νγ''`, and nothing otherwise.
  - If `d > 0`, write `μ = νθ` with `|θ| = d`, so `γ'' = θγ'`. By (W4) the term is
    nonzero only if `γ'` is a prefix of `θ^∞`. If `d < 0`, symmetrically, it is
    nonzero only if `γ''` is a prefix of `θ^∞` with `ν = μθ`.
  - Take `γ = π ε`, with `π` longer than every word in `z_d` and `ε` chosen as in
    Part 3 to avoid these finitely many periodic prefixes. Then `z_d = 0`.
- **Degree 0 is scalar.**
  - Lengthen `z_0 = Σ_(|α|=|β|=L) s_α m_(f_(αβ)) t_β`. Central `z_0` commutes with
    the projections `s_α t_α`, so `s_α m_(f_(αβ)) t_β = (s_α t_α) z_0 (s_β t_β) = 0`
    for `α ≠ β`, and `f_(αβ) = 0`.
  - So `z_0 = m_f` with `f ∈ 𝒜`. From `m_f s_i = s_i m_f` and (W2), `f(iz) = f(z)`,
    so `f(z) = f(0^(n+1) z) = r_(0^n)(0)` at a level `n` of `f`. So `f` is constant.

## Parts 5 and 6

- **Part 5.** The standard Leavitt-family computation. The code gives
  `Σ s_(c_i) t_(c_i) = 1` and `t_(c_i) s_(c_j) = δ_ij`. Restricting to `Q ⊂ C_h`
  gives `M_r(Q) -> C_h`, which is injective by compressing with `t_(c_i)`, `s_(c_j)`.
- **Part 6.**
  - The expansion into `S`, levelwise data in `𝒬`, refinement and products are all
    computable. Zero-testing reduces, after lengthening, to (C3), that is to
    vanishing of finitely many rational functions.
  - `L_Q(1,2) -> C_h` is the unital map from the universal property. It is nonzero
    and `L_Q(1,2)` is simple, so it is injective.

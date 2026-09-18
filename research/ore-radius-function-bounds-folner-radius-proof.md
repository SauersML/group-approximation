---
rg: 2
id: ore-radius-function-bounds-folner-radius-proof
kind: route
title: Localize Bartholdi's garden-of-Eden automaton to a finite support and produce its kernel vector by Ore column elimination
target: ore-radius-function-bounds-folner-radius
requires: []
artifacts:
  - experiments/ore-radius-folner-2026-09-17/check_local_bartholdi.py
---

Notation as in the claim. Fix `k` with `n = |B(k)| >= 3`, write `S' = B(k)`, and let `r = H_n n! + 1`.

**Imported combinatorics.** L. Bartholdi, *Amenability of groups is characterized by Myhill's theorem*,
arXiv:1605.09133v2, with an appendix by D. Kielak. The source was read from the arXiv PDF on 2026-09-17.
Proof of Lemma 2.1, verbatim up to PDF extraction:

> Define Y := {1,...,n} × S_n / (i,σ) ∼ (j,σ) if i and j belong to the same cycle of σ; in other words,
> Y is the set of cycles of elements of S_n. Let X_i be the natural image of {i} × S_n in the quotient Y.

Equation (2.1) and the line after it, verbatim:

> #Y = Σ_{i=1}^n n!/i ≤ (1 + log n) n! since 1 + 1/2 + ··· + 1/n ≤ 1 + log n for all n.

Equation (2.2) and its preamble, verbatim:

> consider I ⊆ {1,...,n} and i ∈ I, and set X_{i,I} := X_i ∖ ⋃_{j∈I∖{i}} X_j. [...] #X_{i,I} = n!/#I.

So `#Y = H_n n!` and `#X_(i,I) = n!/#I`. The artifact recomputes both for `n = 3, ..., 6`.

**Step 0 (alphabet with slack).** Let `Y' = Y ⊔ {*}`, so `#Y' = r`, and identify `{1, ..., n}` with
`S'`. For `s ∈ T ⊆ S'` put `X_(s,T) = X_s ∖ ⋃_(t ∈ T∖{s}) X_t`. Then

`#X_(s,T) = n!/#T >= r / ((1 + ln n) #T)`,

because `n!(1 + ln n - H_n) >= 1` for every `n >= 3`. At `n = 3` the left side is `0.68... · 6 > 1`.
The factor `1 + ln n - H_n` is increasing, since `ln(n+1) - ln n > 1/(n+1)`, and `n!` is increasing. The
inequality fails at `n = 2`, which is why the claim assumes `n >= 3`.

**Step 1 (the matrix).** Let `L ⊇ K` be a field. For each `s ∈ S'` choose an `r × r` matrix `α_s` over
`L` whose rows indexed by `Y' ∖ X_s` are zero. For `s ∈ T` let `α_(s,T)` be the submatrix of `α_s` on the
rows `X_(s,T)`. Call `α` **generic** if for every family `(T_s)_(s∈S')` with `s ∈ T_s ⊆ S'` and
`Σ_s #X_(s,T_s) >= r`, the stacked matrix `(α_(s,T_s))_s`, with `Σ_s #X_(s,T_s)` rows and `r` columns,
has rank `r`.

*Generic matrices exist when `|L| > r 2^(n(n-1))`.* Treat the entries of `α_s` in rows `X_s` as
independent indeterminates. Distinct pairs `(s, y)` index distinct rows, so the stacked matrix of any
family is a matrix of distinct indeterminates with at least `r` rows. Any `r` of its rows have a nonzero
determinant polynomial of degree `r`. There are at most `2^((n-1)n)` families. The product `P` of one
such determinant per family is nonzero of degree at most `r 2^(n(n-1))`. By Schwartz–Zippel, `P` has a
non-root over any field with more than `deg P` elements. For infinite `K` take `L = K`. For finite `K`
take `[L : K] = d = n^2 + ⌈log_2 r⌉ + 1`; then `|L| >= 2^d > r 2^(n^2)`.

Let `M = Σ_(s∈S') α_s s ∈ M_r(L[G])`. Every `X_s` misses `*`, so row `*` of `M` is zero. Let `M'` be the
`(r-1) × r` matrix of the other rows. Its entries lie in `L[B(k)]`, and `ker M = ker M'` on `L[G]^r`.

**Lemma 1 (local Bartholdi injectivity).** Let `α` be generic and let `v ∈ L[G]^r` be nonzero with
`M v = 0`. Let `F = ⋃_j supp v_j`. Then `|S' F| < (1 + ln n)|F|`.

*Proof.* Write `v = Σ_g φ(g) g` with `φ : G -> L^r` supported on `F`. Then
`M v = Σ_h ψ(h) h` with `ψ(h) = Σ_(s∈S') α_s φ(s^-1 h)`. Suppose `|S'F| >= (1 + ln n)|F|`. This is
Bartholdi's argument (§2, proof of Theorem 1.1) with his inequality (2.3) required for the single set
`F` only.
- For `g ∈ S'F` let `ρ(g) = 1/#{t ∈ S' : g ∈ tF}`. Then
  `Σ_(f∈F) Σ_(s∈S') ρ(sf) = Σ_(g∈S'F) Σ_(s : g ∈ sF) ρ(g) = |S'F|`.
- So some `f ∈ F` has `Σ_s ρ(sf) >= 1 + ln n`.
- Put `T_s = {t ∈ S' : sf ∈ tF}`. This contains `s`, and `#T_s = 1/ρ(sf)`.
- By Step 0, `Σ_s #X_(s,T_s) >= Σ_s r ρ(sf)/(1 + ln n) >= r`, so the stacked map
  `a ↦ (α_(s,T_s) a)_s` is injective.
- In `ψ(sf)` only the terms with `t ∈ T_s` contribute, since `t^-1 sf ∈ F` iff `t ∈ T_s`. Each
  `α_t` with `t ≠ s` vanishes on the rows `X_(s,T_s) ⊆ Y' ∖ X_t`. So the projection of `ψ(sf)` to
  `X_(s,T_s)` equals `α_(s,T_s) φ(f)`.
- Since `φ(f) ≠ 0`, some `ψ(sf) ≠ 0`, which contradicts `M v = 0`. ∎

**Lemma 2 (Ore column elimination).** Assume `K[G]` has no zero divisors and `Ω = Ω_(K,S)` is finite.
Let `N` be a `p × q` matrix over `K[B(ρ)]` with `p < q`. Then there is a nonzero `v ∈ K[G]^q` with
`N v = 0` and all entries in `K[B(τ^(p)(ρ) - ρ)]`.

*Proof.* By induction on `p`. For `p = 0` take `v = e_1`. Let `p >= 1`, and note
`τ^(p)(ρ) - ρ >= τ^(p-1)(ρ) - ρ`, since `τ(R) >= R` and `τ` is nondecreasing.

If row 1 of `N` is zero, delete it and apply the case `p - 1`.

Otherwise permute columns so that `N_11 ≠ 0`. For `j = 2, ..., q`:
- if `N_1j = 0`, put `t_j = 1` and `b_j = 0`;
- else the Ore radius gives nonzero `t_j, b_j ∈ K[B(Ω(ρ))]` with `N_1j t_j = N_11 b_j`.

Put `c_j = e_j t_j - e_1 b_j ∈ K[G]^q`, so row 1 of `N c_j` is `N_1j t_j - N_11 b_j = 0`. The other
rows of `N c_j` give the `(p-1) × (q-1)` matrix `N'_ij = N_ij t_j - N_i1 b_j`, with entries in
`K[B(τ(ρ))]`. By induction there is a nonzero `w ∈ K[G]^(q-1)` with `N' w = 0` and entries in
`K[B(τ^(p-1)(τ(ρ)) - τ(ρ))]`.

Let `v = Σ_(j>=2) c_j w_j`, that is, `v_j = t_j w_j` for `j >= 2` and `v_1 = -Σ_j b_j w_j`. Then
`N v = Σ_j (N c_j) w_j`. Its row 1 is `0` and its rows `2..p` are `N' w = 0`. Some `w_j ≠ 0` and
`t_j ≠ 0`, so `v_j = t_j w_j ≠ 0`, because `K[G]` has no zero divisors. The entries of `v` lie in
`K[B(Ω(ρ) + τ^(p-1)(τ(ρ)) - τ(ρ))] = K[B(τ^(p)(ρ) - ρ)]`. ∎

**Proof of Theorem A.**

*Infinite `K`.* Take `L = K` and `α` generic. Lemma 2 with `N = M'`, `p = r - 1`, `q = r`, `ρ = k` gives
a nonzero `v ∈ K[G]^r` with `M v = 0` and support `F ⊆ B(τ^(r-1)(k) - k)`. Lemma 1 gives
`|B(k)F| < (1 + ln n)|F|`.

*Finite `K`.* Let `[L : K] = d` with `α` generic over `L`, and fix a `K`-basis `e_1, ..., e_d` of `L`.
Scalars are central in `L[G]`, so `L[G]^r ≅ K[G]^(rd)` as right `K[G]`-modules. Under this
identification, left multiplication by `λ g` (`λ ∈ L`, `g ∈ G`) is the `d × d` block
`(c_(li) g)`, where `λ e_i = Σ_l c_(li) e_l`. So `M'` becomes an `(r-1)d × rd` matrix over `K[B(k)]`.
Lemma 2 over `K[G]` with `p = (r-1)d` gives a nonzero kernel vector with entries in
`K[B(τ^((r-1)d)(k) - k)]`. The corresponding nonzero `v ∈ L[G]^r` has `M v = 0` and the same support
bound. Lemma 1 is linear algebra over the field `L` and applies without change. ∎

**Scope.**
- Only `K[G]` is assumed to have no zero divisors. `L[G]` is never used as a ring in Lemma 2.
- The constant `r ~ n!` enters only through the elimination depth.
- A version of Lemma 2.1 with `#Y` polynomial in `n` would shrink the depth to a polynomial in `n` and
  strengthen every consequence. Whether one exists has not been examined.

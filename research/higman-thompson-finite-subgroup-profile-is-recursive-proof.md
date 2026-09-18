---
rg: 2
id: higman-thompson-finite-subgroup-profile-is-recursive-proof
kind: route
title: Pump the depth cocycle with explicit constants, count the cones it permutes, and compare with the finite lamp subgroups of the diagonal product
target: higman-thompson-finite-subgroup-profile-is-recursive
requires:
  - short-expander-subgroups-force-folner-growth
  - decidable-amenable-groups-have-no-recursive-folner-bound
---

Notation as in the claim. Words are read from the root. Every `k in Aut(X*)` is
a length-preserving bijection of `X*` and of `C`, with `k(aw) = k(a) k|_a(w)`.
Steps 2–4 follow `almost-automorphism-torsion-subgroups-are-rf-proof`, Steps
0–4, keeping track of the constants.

## Step 1. Depth is subadditive (item 1)

Take representations `g(u_i w) = v_i g_i(w)` and `h(u'_j w) = v'_j h_j(w)` with
all code words of length at most `dep(g)`, `dep(h)` respectively. For each `j`
compare `v'_j` with the code `{u_i}`; exactly one of two cases holds.
- Some `u_i` is a prefix of `v'_j`, say `v'_j = u_i z`. Then on `[u'_j]`,
  `gh(u'_j w) = v_i g_i(z h_j(w)) = v_i g_i(z) · (g_i|_z h_j)(w)`. The new pair
  is `(u'_j, v_i g_i(z))`, with `|v_i g_i(z)| = |v_i| + |v'_j| − |u_i|`.
- `v'_j` is a proper prefix of some `u_i`, say `u_i = v'_j z`. The cones `[u_i]`
  of this kind with `v'_j` as prefix partition `[v'_j]`. For each, put
  `z' = h_j^(−1)(z)`, of length `|z|`. Then
  `gh(u'_j z' w) = v_i g_i((h_j|_(z')) (w))`, with pair `(u'_j z', v_i)` and
  `|u'_j z'| = |u'_j| + |u_i| − |v'_j|`.

The new domain words partition `C`, and so do their images. Every new code
word has length at most `dep(g) + dep(h)`, and the tail maps lie in `G`
because `G` is self-similar. For the inverse, `g^(−1)(v_i w) = u_i g_i^(−1)(w)`.

## Step 2. The depth cocycle

For `h in V_d(G)` and `x in C`, pick a piece `h(uw) = v g(w)` with `x in [u]` and
put `c(h,x) = |v| − |u|`.
- It is well defined. Refining `(u,v,g)` to `(ua, v g(a), g|_a)` keeps
  `|v| − |u|`. Two pieces at `x` have a common refinement `[p]`,
  `h(pw) = q k(w) = q' k'(w)` for all `w`. If `|q'| > |q|`, then `q' = qt` with
  `t` nonempty and `k(w) = t k'(w)` for all `w`, so the bijection `k` of `C`
  would map into `[t]`. So `|q| = |q'|`.
- `c(hh', x) = c(h, h'x) + c(h', x)`, and `|c(h,x)| <= dep(h)`.
- **Fixed points.** If `h` has finite order `N` and `hx = x`, then
  `N c(h,x) = c(h^N, x) = 0`.
- **Contraction.** If `h(Tw) = T y k(w)` for all `w`, with `y` nonempty and
  `k in Aut(X*)`, then `w ↦ T y k(w)` maps the complete space `[T]` into itself
  and multiplies the metric `d^(−|common prefix|)` by `d^(−|y|)`. Its fixed point
  `x*` has `h x* = x*` and `c(h, x*) = |y| > 0`. So `h` has infinite order.

## Step 3. Pumping with explicit constant

Let `Γ = <T>` be finite with `T = T^(−1)` and `dep(s) <= D` for `s in T`. Put
`K = D`, so `|c(s,x)| <= K`, and `B = K d^(D+K) = B(D)`.

**Claim.** `|c(h,x)| <= B` for all `h in Γ` and `x in C`.

Write `h = s_m ⋯ s_1`, `x_0 = x`, `x_i = s_i x_(i−1)`,
`ht(i) = c(s_i ⋯ s_1, x)`. Suppose `M = ht(m) > B` (for `ht(m) < −B` apply the
argument to `h^(−1)` at `hx`).
- For `0 <= ℓ < M` let `t_ℓ = max{ i : ht(i) <= ℓ }`. Then `t_ℓ < m`,
  `ht(t_ℓ) in (ℓ − K, ℓ]`, and `ht(i) > ℓ >= ht(t_ℓ)` for `i > t_ℓ`.
- Each value `v` of `ht(t_ℓ)` serves at most `K` levels `ℓ in [v, v+K)`. So
  there are at least `M/K > d^(D+K)` distinct values, hence as many distinct
  times. Two of them, `t < t'`, have `x_t`, `x_(t')` with the same first `D+K`
  letters `T_*`. Put `r = ht(t') − ht(t) > 0`.
- Write `x_t = T_* z`. By induction for `t <= i <= t'`,
  `x_i = T_i k_i(z)` with `k_i in G`, `|T_i| = D + K + ht(i) − ht(t) >= D`, and
  `T_(i+1)` depends only on `T_i` and `s_(i+1)`. Indeed `s_(i+1)` reads a code
  word `u_j` of length `<= D <= |T_i|`, so `T_i = u_j T'` and
  `s_(i+1)(T_i k_i(z)) = v_j g_j(T') · (g_j|_(T') k_i)(z)`.
- The same computation holds with any `z'` in place of `z`. So
  `h' = s_(t') ⋯ s_(t+1) in Γ` has `h'(T_* z') = T_(t') k(z')` for all `z'`. Here
  `|T_(t')| = D + K + r` and `T_(t')` begins with `T_*`, so `T_(t') = T_* y` with
  `|y| = r > 0`. By Step 2, `h'` has infinite order. This contradicts finiteness
  of `Γ`. `∎`

## Step 4. Counting cones (item 2)

- **Single pieces.** Every `h in Γ` maps every cone `[p]` with
  `|p| >= D + B` onto a cone `[q]` as one piece `pw ↦ q k(w)`, with
  `||q| − |p|| <= B`. Induct on word length in `T`: if `h_0` maps `[p]` onto
  `[q_0]` as one piece, then `|q_0| >= |p| − B >= D` by Step 3, so the next
  generator acts on `[q_0]` through one code word.
- **Action.** Put `n = D + 2B` and `F = { h[p] : h in Γ, |p| = n }`. Its cones
  have depth in `[n − B, n + B]`, so `|F| <= Σ_(j <= n+B) d^j < d^(n+B+1)`.
  Every cone in `F` has depth `>= D + B`, so `Γ` permutes `F` by the previous
  point.
- **Kernel.** If `h` fixes every cone of `F`, then on each `[p]`, `|p| = n`, it
  acts as `pw ↦ p k_p(w)` with `k_p in G`. The map `h ↦ (k_p)_(|p| = n)` is an
  injective homomorphism from the kernel to `G^(d^n)`. The kernel is finite and
  `G` is torsion-free, so the kernel is trivial.
- So `Γ` embeds in `Sym(F)`, and
  `|Γ| <= (d^(n+B+1))! = (d^(D + 3B + 1))! = R_d(D)`. `∎`

## Step 5. Profile bound (item 3)

By Step 1 an element of `S`-length at most `L` has depth at most `D_0 L`. A
finite subgroup generated by such elements has order at most `R_d(D_0 L)` by
Step 4. If `L >= max(d, D_0)` then `d <= L` and `D_0 L <= L^2`, and `R` is
non-decreasing in both arguments, so `R_d(D_0 L) <= R_L(L^2) = R♯(L)`. The
finitely many smaller `L` contribute a constant, which `≼` absorbs.

## Step 6. Item 4

`X^δ <= FS` holds by definition. If `L·U(L^3) ≽ R♯`, then `X^δ_K ≼ L·U(L^3)`, and
the hypothesis of item 4 of `short-expander-subgroups-force-folner-growth` fails.

## Step 7. The diagonal products (item 5)

Recall the construction of `decidable-amenable-groups-have-no-recursive-folner-bound`:
`Δ = Δ_U` is generated by `T_Δ = (τ, α_a, β_b)`, the maps `π_s` embed it in
`Π_s Δ_s` with `Δ_s = Γ_(s) wr Z` (BZ1 there), and in the factor `Δ_s` we have `α_a = a(s)δ_0` and
`β_b = b(s)δ_(k_s)`. Here `k_0 = 0 < k_1 < …` with `k_s = 2·3^s`,
`|Γ_(s)| > s U(s^2 k_s)`, and `A(s) ∪ B(s)` generates `Γ_(s)`.

- **Finite lamp subgroups.** Fix `t >= 1` and let `Q_t` be generated by the
  `α_a` and the `τ^(−k_t) β_b τ^(k_t)`. These have `T_Δ`-length at most
  `2k_t + 1`. In `Δ_s` they are `a(s)δ_0` and `b(s)δ_(k_s − k_t)`. For `s = t`
  they generate `Γ_(t)δ_0 ≅ Γ_(t)`. For `s ≠ t` the positions `0` and
  `k_s − k_t` differ, so they generate `A(s)δ_0 × B(s)δ_(k_s − k_t) ≅ A × B`.
  Under the fixed identifications `A(s) ≅ A`, `B(s) ≅ B`, all factors `s ≠ t`
  see the same map, `a ↦ (a,1)`, `b ↦ (1,b)`. So `Q_t` embeds in
  `Γ_(t) × (A × B)`, and it is finite and surjects onto
  `Γ_(t)`. Hence `|Q_t| > t U(t^2 k_t)`.
- **Contradiction.** Suppose `ι : Δ → V_d(G)` is injective, with `G`
  torsion-free self-similar. Put `S = ι(T_Δ)` and `D_0 = max dep(s)`. Then
  `ι(Q_t)` is a finite subgroup generated by elements of `S`-length at most
  `2k_t + 1`. For `t >= 2` with `2k_t + 1 >= max(d, D_0)`, Step 5 gives
  `|Q_t| <= R♯(2k_t + 1)`. But
  `|Q_t| > t U(t^2 k_t) >= R♯(t^2 k_t) >= R♯(2k_t + 1)`, since
  `t^2 k_t >= 4k_t >= 2k_t + 1` and `R♯` is non-decreasing. This is a
  contradiction. `∎`

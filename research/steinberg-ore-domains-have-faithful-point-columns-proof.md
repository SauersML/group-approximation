---
rg: 2
id: steinberg-ore-domains-have-faithful-point-columns-proof
kind: route
title: The points killed by a nonzero element form a clopen set; compactness and the Ore condition produce one nonzero element killing every point column, and the point columns jointly separate elements
target: steinberg-ore-domains-have-faithful-point-columns
requires: []
---

Notation as in the target. Throughout, for a subring `C` and `a ∈ C`, `Ca = { ca : c ∈ C }`.

## Step 0 (iterated Ore)

**Claim.** If `C` is a domain with the left Ore condition and `c_1, ..., c_r ∈ C` are nonzero, then there is
a nonzero `h ∈ Cc_1 ∩ ... ∩ Cc_r`.

**Proof.** Induct on `r`. The case `r = 1` is `h = c_1 c_1 ≠ 0`. For the step, suppose `d ≠ 0` lies in
`Cc_1 ∩ ... ∩ Cc_(r-1)`. By the Ore condition there is a nonzero `h = c'd = c''c_r` with `c', c'' ∈ C`.
- Write `d = e_j c_j` for each `j < r`. Then `h = (c'e_j) c_j ∈ Cc_j`.
- Also `h ∈ Cc_r`.

A commutative domain is left Ore, since `ab = ba ∈ Ca ∩ Cb` and `ab ≠ 0`.

## Part 2 (crossed products)

Every `b ∈ B` is uniquely `Σ_p f_p v_p`, with finitely many nonzero `f_p ∈ LC(X, k)`.

**2a. `π_x` is a representation.** Set `π_x(f v_p) δ_q = f(pq·x) δ_(pq)` and extend linearly. It
suffices to check `π_x((f v_p)(g v_q)) = π_x(f v_p) π_x(g v_q)` on each `δ_r`. The left side is computed
from `(f v_p)(g v_q) = f (p·g) v_(pq)`:

`π_x(f (p·g) v_(pq)) δ_r = f(pqr·x) (p·g)(pqr·x) δ_(pqr) = f(pqr·x) g(qr·x) δ_(pqr)`.

The right side is

`π_x(f v_p)(g(qr·x) δ_(qr)) = g(qr·x) f(pqr·x) δ_(pqr)`.

The two agree. Also `π_x(1) = π_x(1 v_e) = id`.

**2b. The column.** `π_x(b) δ_e = Σ_p f_p(p·x) δ_p`. Hence `π_x(b) δ_e = 0` iff `x ∉ Z(b)`, where

`Z(b) = ⋃_p p^(-1) · { f_p ≠ 0 }`.

Each `{ f_p ≠ 0 }` is clopen, because `f_p` is locally constant, and `p^(-1)` acts by a homeomorphism. The
union is finite, so `Z(b)` is clopen.

**2c. Columns separate.** If `π_x(b) δ_e = 0` for every `x`, then `f_p(p·x) = 0` for all `p, x`. Since
`x |-> p·x` is onto, every `f_p = 0`, so `b = 0`.

**2d. The Ore argument.** Suppose, for contradiction, that for every `x ∈ X` some nonzero `c_x ∈ C` has
`π_x(c_x) δ_e = 0`.
1. Then `x ∈ X ∖ Z(c_x)`, which is open. By compactness, finitely many `c_1, ..., c_r` satisfy
   `X = ⋃_j (X ∖ Z(c_j))`.
2. By Step 0 take a nonzero `h ∈ ⋂_j Cc_j`.
3. Let `x ∈ X` and choose `j` with `x ∉ Z(c_j)`. Write `h = a c_j` with `a ∈ C`. Then
   `π_x(h) δ_e = π_x(a) π_x(c_j) δ_e = 0`.
4. So `π_x(h) δ_e = 0` for every `x`, and 2c gives `h = 0`, a contradiction.

Hence some `x` has `π_x(c) δ_e ≠ 0` for every nonzero `c ∈ C`. By linearity, `c |-> π_x(c) δ_e` is
injective on `C`.

## Part 1 (ample groupoids)

**1a. The regular column modules.** `𝒢` is ample, so `s` and `r` are local homeomorphisms and every fibre
`𝒢_η` is discrete.
- An element `f ∈ A_k(𝒢)` is a finite combination of characteristic functions of compact open bisections.
  So `supp f = { f ≠ 0 }` is open, closed (since `f` is locally constant) and contained in a compact set.
  Hence `supp f` is compact open.
- A compact set meets the closed discrete set `𝒢_η` in finitely many points. So the sums
  `f · δ_γ = Σ_(s(α) = r(γ)) f(α) δ_(αγ)` are finite.
- They define a module. Both `(f * g) · δ_γ` and `f · (g · δ_γ)` equal `Σ_(α, β) f(α) g(β) δ_(αβγ)`,
  summed over composable `α, β` with `s(β) = r(γ)`.

**1b. The column.** For `ξ ∈ 𝒢_η`, `(c · δ_η)(ξ) = c(ξ)`, since the only `α` with `αη = ξ` is
`α = ξ`. So `c · δ_η = c|_(𝒢_η)`, and `c · δ_η = 0` iff `η ∉ s(supp c)`.
- `s(supp c)` is compact, as a continuous image of a compact set, hence closed in the Hausdorff space
  `𝒢^(0)`.
- So `{ η : c · δ_η = 0 }` is open.

**1c. Columns separate.** If `h · δ_η = 0` for every `η`, then `h` vanishes on every `𝒢_η`, so `h = 0`.

**1d.** Repeat 2d word for word: replace `X` by the compact space `𝒢^(0)`, `π_x(·) δ_e` by `(·) · δ_η`,
and 2c by 1c.

## Part 3 (growth)

**3a. Crossed products.**
- For `b = Σ f_p v_p` and `b' = Σ g_q v_q`, `b b' = Σ_(p,q) f_p (p·g_q) v_(pq)`. So
  `supp(bb') ⊆ supp(b) supp(b')`.
- A product of `j <= n` elements of `S` therefore has support in `B_P(jm) ⊆ B_P(mn)`. The same holds for
  every element of `V_n(S)`.
- For such `b`, 2b gives `π_x(b) δ_e ∈ span{ δ_p : p ∈ B_P(mn) }`.
- Take `x` from Part 2. The map `c |-> π_x(c) δ_e` is injective on `C ⊇ V_n(S)`, so
  `dim V_n(S) <= |B_P(mn)|`.

**3b. Groupoids.**
- For compact open bisections `U, U'`, `χ_U * χ_(U')` is `χ_(UU')`, and `UU'` is again a compact open
  bisection.
- So every product of between `1` and `n` elements of `S` lies in
  `span{ χ_W : W = U_1 ⋯ U_j, 1 <= j <= n, U_i ∈ 𝒰 }`.
- A bisection `W` meets `𝒢_η` in at most one point `γ_W`, and `χ_W · δ_η` is `δ_(γ_W)` or `0`.
- So `V_n(S) · δ_η ⊆ span{ δ_γ : γ ∈ W_n ∩ 𝒢_η }`. Injectivity from Part 1 gives the bound.

## Part 4 (hosted groups)

1. `C = φ(k[G])` is a ring isomorphic to `k[G]`, so it is a nonzero left Ore domain.
2. Put `S = φ(T ∪ {e})`, and take `m` as in Part 3 (at least `1`).
3. For `n >= 1`, every `g ∈ B_G(n)` is a product of between `1` and `n` elements of `T ∪ {e}`. So
   `φ(g) ∈ V_n(S)`.
4. The `φ(g)` are linearly independent, because `φ` is injective.
5. So `|B_G(n)| <= dim V_n(S) <= |B_P(mn)|`.

## Part 5 (polynomial growth)

**5a. GK dimension.** Measure `GKdim C` by `sup_S limsup_n log dim V_n(S) / log n` over finite `S ⊆ C`.
Part 3 gives `dim V_n(S) <= K m^D n^D`, so `GKdim C <= D`.

**5b. No `k[Z^(D+1)]`.** Let `φ : k[Z^(D+1)] -> B` be injective.
1. The image `C` is a commutative domain, hence left Ore (Step 0).
2. Take `S = φ({1, t_1^(±1), ..., t_(D+1)^(±1)})`.
3. For `n >= 1`, each monomial `t^a` with `a_i >= 0` and `Σ a_i <= n` is a product of between `1` and `n`
   elements of `{1, t_i}`. Their images are linearly independent.
4. So `dim V_n(S) >= binom(n + D + 1, D + 1) >= n^(D+1) / (D+1)!`.
5. Part 3 gives `dim V_n(S) <= K m^D n^D`. For large `n` this contradicts step 4.

For `P = Z^2`, `|B_P(N)| = 2N^2 + 2N + 1 <= 5 N^2` for `N >= 1`, so `D = 2`, and `k[Z^3]` does not embed.

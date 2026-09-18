---
rg: 2
id: resolvent-presentation-ring-is-residually-finite-proof
kind: route
title: Twisted-shift finite modules separate R_l, by the path normal form and generic density in F_l[Z * C_m]
target: resolvent-presentation-ring-is-residually-finite
requires:
  - resolvent-ring-has-path-normal-form
---

Lane proof, for every prime `l`. Notation of `resolvent-ring-has-path-normal-form`.

**The finite modules.** Take:
- `r >= 1`, and `N >= 1` with `l^(r-1) | N`;
- `d >= 1`, `g in GL_d(Z/l^r)` and an idempotent `E in M_d(Z/l^r)`.

On `M = ⊕_(j in Z/N) V_j`, with each `V_j = (Z/l^r)^d`, let:
- `u = lj` on `V_j`;
- `x : V_j -> V_(j-1)` be the identity for `j != 0`, and `x : V_0 -> V_(N-1)` be `g`;
- `B = (u+1)^(-1)`;
- `e = E` on `V_0` and 0 elsewhere.

The eight relations hold. The only nontrivial check is `x u = (u+l) x` at the wrap:
`u = 0` on `V_0`, and `u + l = lN ≡ 0 (mod l^r)` on `V_(N-1)`. So `M` is a finite
module over `R_l`. Write `(r, N, g, E)` for it.

**Action of the path basis.** Let `N` divide every `k_i`. Write `a = Nα + ρ`,
`b = Nβ + ρ'` with `0 <= ρ, ρ' < N`.
- `x^N = g` on every `V_j`, and `e x^k e = E g^(k/N) E` on `V_0`.
- `[a|K|b]` maps `V_(ρ')` to `V_(-a mod N)` by the matrix

      w_(a,K,b)(g,E) = g^(⌈a/N⌉) E g^(k_1/N) E ... E g^(k_s/N) E g^(β),

  and kills the other `V_j`.
- If `N ∤ k_i` for some `i`, then `[a|K|b]` acts as 0.
- `(a, b) -> (a mod N, ⌈a/N⌉, b mod N, ⌊b/N⌋)` is injective.

**Density lemma.** Let `m = 2` if `l` is odd and `m = 3` if `l = 2`. Let `ε` be the
idempotent `(1+s)/2`, respectively `1+s+s^2`, of `F_l[C_m] = F_l[s]`. Then:
- `ε != 0, 1`;
- `ε` has a nonzero coefficient `c` at some `g* != 1`.

For finitely many distinct tuples `(α; n_1..n_s; β)` with all `n_i != 0`, the
elements `z^α ε z^(n_1) ε ... ε z^(n_s) ε z^β` of `F_l[Z * C_m]` (`z` a generator of
`Z`) are linearly independent.
- Suppose `Σ λ_τ w_τ = 0` with some `λ_τ != 0`. Choose `τ*` with `λ_(τ*) != 0` and the
  largest number `s+1` of `ε`'s.
- Expand each `ε`. The reduced word `z^α g* z^(n_1) g* ... g* z^β` has `s+1` letters from
  `C_m` (the `n_i` are nonzero). It occurs only in the expansion of `w_(τ*)`, with
  coefficient `c^(s+1)`: terms with a letter `1`, or with fewer `ε`'s, reduce to at
  most `s` such letters, and reduced forms in free products are unique.
- So its coefficient is `λ_(τ*) c^(s+1) != 0`, a contradiction.

`Z * C_m` is residually finite because it is virtually free. The kernel of the map
`Z * C_m -> C_m` that kills `z` and is the identity on `C_m` has index `m` and meets
every conjugate of `C_m` trivially, so it is free by the Kurosh subgroup theorem. Free
groups are residually finite, and so are finite extensions of residually finite groups
(intersect the conjugates of a finite-index normal subgroup). Pointer, not needed:
Gruenberg, *Residual properties of infinite soluble groups*, Proc. LMS (3) 7 (1957),
Theorem 4.1, Corollary (ii), p. 44, for free products in general (location from a
search record only).
- So some finite quotient `Q` is injective on the finitely many group elements in the
  expansions.
- In the regular representation of `F_l[Q]` the images stay independent: the
  coefficient argument survives, since distinct elements stay distinct.
- This gives `d = |Q|`, `g_0 in GL_d(F_l)` and an idempotent `E_0` realizing any finite
  independent family of words.

**Separation.** Let `0 != X in R_l`. Write `X = δ + Σ_(τ in F) c_τ [τ]` with `δ in D`,
`F` finite and `0 != c_τ in G_τ`.
- **Case δ != 0.** Use `E = 0`, so `e` acts as 0 and `X` acts as `δ`, with `d = 1`,
  `g = 1`. Write `δ = Σ_k x^k f_k` with some `f_k != 0`. Pick an integer `t` with
  `f_k(lt) != 0` (a rational function has finitely many zeros), `r` with
  `f_k(lt) ∉ l^r Z_(l)`, and `N` a multiple of `l^(r-1)` larger than the spread of the
  `k`. Applied to the basis vector `f_t` of `V_t`, the `k`-term of `δ` gives
  `f_k(lt) f_(t-k)`, and the other terms land in other copies. So `δ f_t != 0`.
- **Case δ = 0.** Let `ν = min_τ v_l(c_τ)` and `F_0 = {τ : v_l(c_τ) = ν}`. For
  `τ in F_0` with `s >= 1`, `ν < min m_(k_i)`, so `l^ν | k_i` for all `i`.
  - Take `r = ν+1` and `N = l^ν`.
  - By the density lemma choose `(g_0, E_0)` over `F_l` so that, for each pair of
    copies, the words `w_τ`, `τ in F_0`, landing in that pair are independent.
  - Lift `g_0` to `GL_d(Z/l^r)`, and `E_0` to an idempotent (idempotents lift modulo
    the nilpotent ideal `l`).
  - In `(r, N, g, E)` every `τ ∉ F_0` acts as 0: either `l^(ν+1) | c_τ`, or some `k_i`
    is not divisible by `N`.
  - `X` acts as `l^ν Y`, where `Y = Σ_(τ in F_0) c'_τ w_τ` (placed in blocks) and the
    `c'_τ = c_τ / l^ν` are units.
  - `Y ≢ 0 (mod l)` by independence, so `l^ν Y != 0` in `M_(Nd)(Z/l^(ν+1))`.

So every nonzero `X` survives in a finite quotient of `R_l`. ∎

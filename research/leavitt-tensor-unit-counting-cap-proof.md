---
rg: 2
id: leavitt-tensor-unit-counting-cap-proof
kind: route
title: Monomial expansion, a padding witness and one counting quantifier bound every Leavitt tensor linear group; integral letters attain C_=P
target: leavitt-tensor-unit-word-problems-have-one-counting-quantifier
requires:
  - leavitt-square-units-wp-complexity-proof
  - prime-field-leavitt-square-units-mod-p-proof
---

Lane proof (bh-free-26), elementary. It extends §6 of `leavitt-square-units-wp-complexity-proof`
(below, "the `F_2` route") to `k` factors, `L(1,n)` factors, matrices, and the coefficient
rings `F_q` and `Z[1/M]`.

## 1. Monomials and depth

In factor `j`, write `s^(j)_α`, `t^(j)_α` for the products along a word `α` over
`{0, ..., n_j - 1}`. The algebra `A_K` is spanned over `K` by monomials

`m = ⊗_j s^(j)_(α'_j) t^(j)_(α_j)`,   of length `|m| = Σ_j (|α'_j| + |α_j|)`.

A product of two monomials is `0` or a monomial of length at most the sum, because
`t_β s_γ` is `s_(γ')` or `t_(β')` or `0` according to prefix comparison.

Fix a finite generating set of `Γ`. Write each generator and its inverse as a matrix of fixed
sums of monomials. A word `W` of length `ℓ` is then an `N × N` matrix. Each entry of `W - I` is a
sum over *paths*. A path is a choice, for each letter, of a matrix index and a monomial.
There are at most `C^ℓ` paths. Each contributes a coefficient, a product of `ℓ` fixed
coefficients, times a monomial of length `≤ D = cℓ`.

## 2. The witness lemma for k factors

Refine each monomial in each factor using `1 = Σ_(|γ| = r) s_γ t_γ`, so that every `α_j`
has length exactly `D`. Then every entry `X` of `W - I` is `Σ_(α⃗) Y_(α⃗) t_(α⃗)`, with
`α⃗ = (α_1..α_k)`, `|α_j| = D`, and `Y_(α⃗) = X s_(α⃗)` a combination of pure products
`s_(α⃗')` with `|α'_j| <= 2D`.

Let `ε = 0 1^(3D) 0`. By the argument of the `F_2` route, the cylinders `[α' ε]` for distinct
`α'` of length `≤ 2D` are pairwise disjoint in `{0..n_j-1}^N`. The argument uses only the
letters `0` and `1`, so it holds for every `n_j >= 2`. Products of such cylinders are pairwise
disjoint too. So `Y_(α⃗) 1_(Π_j [ε])` has, on each such product cylinder, the coefficient of
the corresponding `s_(α⃗')`.

Hence, over **any** coefficient ring `K`, `X = 0` in `A_K` iff `X f_(α⃗) = 0` for all `α⃗`, where
`f_(α⃗) = 1_(Π_j [α_j ε])` in the module `C(Π_j {0..n_j-1}^N, K)`. The module need not be
faithful for this: a zero test value forces all coefficients to vanish. Each `X f_(α⃗)` is
constant on product cylinders of depth `5D + 2`. So `W = I` iff

`(X f_(α⃗))(z) = 0`   for every entry `X`, all `α⃗`, and all points `z` of the form
`(prefix of length 5D+2) 0^∞` in each coordinate.   (T)

A test instance `(entry, α⃗, z)` has `O(ℓ)` bits. `(X f)(z)` is the sum over paths of
`coefficient × f(ψ_path(z))`, minus the identity term. Here `ψ_path(z)` is computed in
polynomial time by tracking `z` backwards through the prefix conditions of the path.

## 3. Coefficients

- **`K = F_q`, `q = p^r`.** Fix an `F_p`-basis of `F_q`. Each basis coordinate of a path's
  coefficient is computable in polynomial time. A coordinate of `(X f)(z)` is a count mod `p`
  with multiplicities in `{0..p-1}`. So "`(X f)(z) = 0`" is a conjunction of `r` coMod_pP
  predicates, hence one `Mod_pP` predicate for prime `p` (Beigel--Gill closure). With the
  universal quantifier over test instances, `WP(Γ) ∈ ∀·Mod_pP`.
- **`K = Z[1/M]`.** A path coefficient is `c/M^e` with `e <= cℓ` and `|c| <= C^ℓ`. So
  `g = M^(cℓ) (X f)(z)` is a `GapP` function of the instance, and "`(X f)(z) = 0`" is
  `C_=P`. The universal quantifier is absorbed: `∀ i: g_i = 0` iff `Σ_i g_i^2 = 0`, and `GapP`
  is closed under products and exponential sums. So `WP(Γ) ∈ C_=P`.

This proves parts 1 and 2.

## 4. Attainment

- **Finite fields.** `L_(F_p)(1,2)^(⊗2) ⊆ L_(F_q)(1,2)^(⊗2)`, so the group `Γ_p` of
  `prime-field-leavitt-square-units-mod-p-proof` sits in the `F_q` host. Its hardness words
  keep their meaning, since the count `N_Q(x)` lies in `F_p ⊆ F_q`.
- **Integers.** Every letter of `Λ_p` is defined over `Z`, with an inverse over `Z`:
  - `T(u,1,v) = 1 + a_u a_v^*` has inverse `1 - a_u a_v^*`;
  - `u_0 = 1 + a_1 a_0^*` has inverse `1 - a_1 a_0^*`;
  - `δ_e`, `*` and the monomial units are defined over `Z`.

  Let `Λ_Z` be these letters and `Γ_Z = <Λ_Z> <= (L_Z(1,2)^(⊗2))^x`. The computations of
  §§1, 2 and 4 of the mod-`p` route are identities in `L_Z(1,2)^(⊗2)`. By §2 above, an element
  is `0` iff it acts as `0` on `C(C × C, Z)`. So `W_Q = 1 + a_c X_Q a_d^*`, where `X_Q` is
  multiplication by the integer `N_Q(x) = #{y : Q(x,y) = 1}`.

  For circuits `Q_1, Q_2` with the same input length for `x`,
  `(a_c X_1 a_d^*)(a_c X_2 a_d^*) = 0` because `a_d^* a_c = 0`. So

  `W_(Q_1) W_(Q_2)^(-1) = (1 + a_c X_1 a_d^*)(1 - a_c X_2 a_d^*) = 1 + a_c (X_1 - X_2) a_d^*`,

  which is `1` iff `N_(Q_1)(x) = N_(Q_2)(x)` for all `x`.

  Every `C_=P` language has the form `{w : f(w) = g(w)}` with `f, g ∈ #P`, so it is
  `{w : #{y : Q_1(w,y)} = #{y : Q_2(w,y)}}` for polynomial-time `Q_i`. Take `x` empty. The map
  `w ↦ W_(Q_(1,w)) W_(Q_(2,w))^(-1)` is a polynomial-time many-one reduction to `WP(Γ_Z)`. With
  part 2, `WP(Γ_Z)` is `C_=P`-complete.

## 5. The barrier

`PSPACE`-hardness of `WP(Γ)` together with part 1 gives `PSPACE ⊆ ∀·Mod_pP`. Together with
part 2 it gives `PSPACE ⊆ C_=P ⊆ PP ⊆ PSPACE`.

---
rg: 2
id: leavitt-nonnegative-part-is-matrix-union-over-free-algebra-proof
kind: route
title: Block the nonnegative monomials by their t-length, restrict a commutative domain to the image of a minimal-rank element, and import Cohn--Schofield for rank one
target: leavitt-nonnegative-part-is-matrix-union-over-free-algebra
requires: []
artifacts:
  - experiments/leavitt-nonnegative-part-2026-09-19/check_matrix_union.py
---

Notation is as in the target. `s_w = s_(w_1) ... s_(w_l)`, `t_w = t_(w_l) ... t_(w_1)`, so `t_w s_w = 1`.

## 0. The free algebra embeds in L

`L` acts on `V = k[N]` (basis `e_n`) by
- `s_i e_n = e_(2n+i)`;
- `t_i e_n = e_((n-i)/2)` if `n ≡ i (mod 2)`, and `t_i e_n = 0` otherwise.

Check the relations.
- `t_i s_j e_n = t_i e_(2n+j) = δ_ij e_n`.
- `Σ_i s_i t_i e_n = e_n`, because exactly one `i` has `n ≡ i`.

So this is an `L`-module. For a word `w = w_1 ... w_l`, `s_w e_1 = e_m`, where the binary digits of `m`, from
the top, are `1, w_l, w_(l-1), ..., w_1`. The operator `s_(w_l)` acts first.

Distinct words give distinct `m`. So the `s_w` are linearly independent, and `x_i ↦ s_i` embeds `P` in `L`.
This embedding is standard for path algebras inside Leavitt path algebras; the module gives a self-contained
proof.

## 1. Matrix blocks (Statement 1)

- **Homomorphism.** For `|u| = |v| = |u'| = |v'| = N` we have `t_v s_(u') = δ_(v,u')`. Hence
  `(s_u p t_v)(s_(u') q t_(v')) = δ_(v,u') s_u p q t_(v')`. So `Φ_N` is multiplicative.
- **Unital.** `Φ_N(1) = Σ_(|u|=N) s_u t_u = 1`, by induction from `s_0 t_0 + s_1 t_1 = 1`.
- **Injective.** `t_u Φ_N((p)) s_v = p_uv(s)`, and `p ↦ p(s)` is injective by §0.

## 2. Union (Statement 2)

**Grading.** The relations are homogeneous for `deg s_i = 1`, `deg t_i = -1`, so `L` is `Z`-graded. Using
`t_i s_j = δ_ij`, every word in the generators reduces to `0` or to some `s_a t_b`. So
`L_n = span{s_a t_b : |a| - |b| = n}`.

**`L_(>=0) ⊆ ∪ E_N`.** Take `s_a t_b` with `|a| >= |b| = N`. Write `a = u w` with `|u| = N`. Then
`s_a t_b = s_u s_w t_b = Φ_N(x_w e_(u,b)) ∈ E_N`.

**`E_N ⊆ E_(N+1)` and `E_N ⊆ L_(>=0)`.**
- For `p ∈ P`, `s_u p t_v = Σ_x s_u p s_x t_x t_v`, which is `Σ_x s_u (p s_x) t_(vx)` as elements of `L`.
- `p x_x` has no constant term, so `p x_x = Σ_y x_y ∂_y(p x_x)`.
- Hence `s_u p t_v = Σ_(x,y) s_(uy) ∂_y(p x_x) t_(vx)`, which lies in `E_(N+1)`. Its block is exactly `ψ(p)`.
- Each `s_u x_w t_v` has degree `|w| >= 0`, so `E_N ⊆ L_(>=0)`.

## 3. Minimal-rank reduction (Statement 3)

View `M_n(D)` as the right-`D`-linear endomorphisms of the column space `D^n`, and let `rank` be `D`-dimension
of the image. Choose `c_0 ∈ C ∖ 0` of minimal rank `r >= 1`, and let `W = c_0(D^n)`, so `dim_D W = r`.

Take any `d ∈ C ∖ 0`.
- `d c_0 ≠ 0`, because `C` has no zero divisors. So `rank(d c_0) >= r`.
- `d(W) = (d c_0)(D^n) = (c_0 d)(D^n) ⊆ W`.
- So `d(W)` is a subspace of `W` of dimension `>= r = dim W`. Hence `d(W) = W`.
- Then `d|_W` is a surjective endomorphism of a finite-dimensional `D`-space, so it is bijective.

The restriction `ρ : C → End_D(W) ≅ M_r(D)` is a `k`-algebra homomorphism, possibly non-unital. It is
injective, and `ρ(d)` is invertible for every `d ≠ 0`.

The inverses `ρ(d)^(-1)` commute with `ρ(C)` and with each other. So `ρ(c)/ρ(d) ↦ ρ(c) ρ(d)^(-1)` is a
well-defined injective homomorphism `Frac(C) → M_r(D)`. Its image `F` is a field containing
`1 = ρ(d)ρ(d)^(-1)` and `λ · 1 = ρ(λ d) ρ(d)^(-1)` for `λ ∈ k`. ∎

## 4. Rank one (Statement 4): citation import

Source: H. Derksen and J. Volčič, *Invariants of finite groups acting on (free) skew fields*, arXiv:2512.03223
(December 4, 2025), §5.2. Read from the PDF on September 19, 2026.
- Standing convention (§2), verbatim: "Throughout this paper let k be a fixed ground field."
- §5.2, verbatim: "The centralizer of a non-scalar element in a free skew field is commutative [C78, Corollaire
  2], and furthermore finitely generated of transcendence degree 1 over k [S85b, Theorem 11.6]. That is, every
  centralizer of a non-scalar element is isomorphic to the function field of a curve."
- Here [C78] is P. M. Cohn's 1978 paper and [S85b] is A. H. Schofield, *Representations of rings over skew
  fields*, 1985. Non-scalar means not in `k`.

**Use.** Let `F ⊆ D` be a commutative subfield containing `k`.
- If `F` is algebraic over `k`, then `trdeg F = 0`.
- Otherwise pick `a ∈ F ∖ k`. Since `F` is commutative, `F ⊆ C_D(a)`, which has transcendence degree 1. ∎

## 5. Consequences

**(a)** Suppose `a, b ∈ L_(>=0)` commute and are independent.
- Some `E_N` contains both. Via `Φ_N^(-1)` and `P ⊆ D` (the free skew field is the universal field of
  fractions of `P`), `C = k[a, b]` becomes a polynomial ring inside `M_(2^N)(D)`.
- §3 gives a subfield `F ≅ k(x, y)` in `M_r(D)`.
- §4 forces `r >= 2`.

**(b)** The involution `*` of `L` (`s_i ↔ t_i`, `k`-linear, reversing products) maps `L_(<=0)` onto `L_(>=0)`.
- For commuting `a, b` we have `P(a, b)^* = P(a^*, b^*)`, because the monomials `a^i b^j` are reversed and
  `a^*, b^*` commute.
- So independence is preserved, and (a) applies.

**(c)** This is immediate from (a) and (b).

**(d)** `M_m(E_N) = Φ(M_(m 2^N)(P)) ⊆ M_(m 2^N)(D)`, which is directly finite. So `L_(>=0)` is stably finite.
- Suppose `φ : L → L_(>=0)` were unital.
- Then `φ(t_0)φ(s_0) = 1` gives `φ(s_0)φ(t_0) = 1`.
- So `φ(s_1 t_1) = 0`, hence `φ(s_1) = φ(s_1 t_1 s_1) = 0`, hence `1 = φ(t_1 s_1) = 0`. This is absurd. ∎

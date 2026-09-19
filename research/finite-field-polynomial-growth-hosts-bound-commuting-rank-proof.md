---
rg: 2
id: finite-field-polynomial-growth-hosts-bound-commuting-rank-proof
kind: route
title: Each basis vector has a low-degree annihilating polynomial because balls grow like r^s; over a finite field the product of all low-degree polynomials annihilates every vector at once
target: finite-field-polynomial-growth-hosts-bound-commuting-rank
requires: []
---

Throughout, `F` is a finite field, and "algebra" means `F`-algebra.

## Theorem A

1. **Monomials have linear propagation.** Composing operators adds propagations,
   and `1` has propagation `0`. So for a monomial `t^a` of total degree `|a| <= K`,
   every `π_α(x^a)` has propagation `<= bK`.
2. **Local evaluation.** Let `D_K ⊆ F[t_1, …, t_m]` be the polynomials of total
   degree `<= K`, so `dim D_K = binom(K + m, m) >= K^m / m!`. Fix `α` and `y ∈ Y_α`.
   The linear map `ev_y : D_K -> F^(Y_α)`, `g ↦ π_α(g(x)) e_y`, lands in
   `span{e_z : d_α(y, z) <= bK}`, of dimension `<= C(1 + bK)^s`.
3. **Uniform `K`.** Since `m >= s + 1`, choose `K` with `K^m / m! > C(1 + bK)^s`.
   This `K` does not depend on `α` or `y`. Then `ev_y` has nonzero kernel. Choose
   `0 != g_y ∈ D_K` with `π_α(g_y(x)) e_y = 0`.
4. **One polynomial for all vectors.** `F` is finite, so `D_K` is a finite set. Put
   `q = ∏_{0 != g ∈ D_K} g`. It is nonzero because `F[t]` is a domain.
5. **It annihilates everything.** The `x_i` commute, so `g ↦ g(x)` is a ring
   homomorphism `F[t] -> R`. For each `α` and `y`, write `q = h_y g_y`. Then
   `π_α(q(x)) e_y = π_α(h_y(x)) π_α(g_y(x)) e_y = 0`.
   - So `π_α(q(x)) = 0` for every `α`.
   - The family is faithful, so `q(x) = 0`. ∎
6. **Consequences.**
   - A polynomial ring `F[x_1, …, x_{s+1}]` with the unit of `R` would give `s + 1`
     commuting algebraically independent elements. This is impossible whenever the
     `x_i` have bounded propagation, which holds in all the applications below.
   - Non-unital subrings and corners reduce to this case by the extension in (B3).
   - A finitely generated commutative subalgebra `S`, with `1` adjoined, has
     `dim S` algebraically independent elements by Noether normalisation. So
     `dim S <= s`.
   - `F[Z^{s+1}] ⊇ F[t_1, …, t_{s+1}]`.

## Corollary B

1. **Crossed products.** Use the convention `δ_g f δ_g^{-1} = f ∘ g^{-1}`. For
   `x ∈ X`, let `π_x` act on `F^(Γ)` by `π_x(f) e_h = f(hx) e_h` and
   `π_x(δ_g) e_h = e_{gh}`.
   - Covariance: `π_x(δ_g) π_x(f) π_x(δ_g)^{-1} e_h = f(g^{-1} h x) e_h = π_x(f ∘ g^{-1}) e_h`.
   - So `π_x(Σ_g f_g δ_g) e_h = Σ_g f_g(ghx) e_{gh}`, and `π_x(1) = id`.
   - *Faithful:* if every `π_x(a)` kills `e_1`, then `f_g(gx) = 0` for all `x`.
     Since `g` is a bijection of `X`, each `f_g = 0`.
   - *Metric:* take the right-invariant word metric `d(h, h') = |h h'^{-1}|`, whose
     balls have the same size as those of `B_Γ`. Then `f δ_g` has propagation
     `<= |g|`. So every element has finite propagation, uniformly in `x`.
   - Theorem A applies with the growth `s` of `Γ`.
2. **Matrices and locally finite tensors.** Commuting elements `x_1, …, x_m` of
   `(LC(X) ⋊ Γ) ⊗ D` involve finitely many elements of `D`.
   - Let `D'` be the unital subalgebra they generate with `1`. It is finite
     dimensional, since `D` is locally finite.
   - The left regular representation gives a unital embedding `D' ↪ M_N(F)`, with
     `N = dim D'`.
   - Tensor products over a field preserve injectivity. So
     `(LC(X) ⋊ Γ) ⊗ D' ↪ M_N(LC(X) ⋊ Γ)`, unitally.
   - `M_N(LC(X) ⋊ Γ)` acts faithfully and unitally on `F^(Γ × [N])` through the
     `π_x^{⊕N}`. Use the metric `d((h,i), (h',j)) = |h h'^{-1}|`, with balls of size
     `<= N C (1 + r)^s`. A matrix has propagation `<=` the maximum over its entries.
   - Theorem A gives `q` with `q(x) = 0` in `M_N(…)`. Pulling back along the
     injective unital maps gives `q(x) = 0` in the tensor product. Matrix algebras
     are the case `D = M_N(F)`.
3. **Corners.** Let `p ∈ R` be idempotent, and let `x_1, …, x_m ∈ pRp` commute and
   be algebraically independent in the unital ring `pRp`.
   - Put `y_i = x_i + (1 - p)`. These commute.
   - For every `g`, `g(y) = g_p(x) + g(1, …, 1)(1 - p)`, where `g_p` is evaluated
     with unit `p`. So `g(y) = 0` forces `p g(y) p = g_p(x) = 0`, hence `g = 0`.
   - The `y_i` have finite propagation, so Theorem A applied to `R` excludes
     `m >= s + 1`. Units in a corner are handled the same way. ∎(B)
4. **The gauge core.** `L(E_d)` is unital, since `E_d` is finite. Its unit, the sum
   of the vertices, has degree `0`, and its core `L(E_d)_0` is locally finite (see
   "Host applications" in `algebraic-core-gradings-bound-homogeneous-laurent-rank-proof`).
   Apply (B2) with `Γ = Z^2`, `s = 2` and `D = L(E_d)_0`.

## Corollary C

1. **Grading.** `H = B_Ω ⊗ L(E_d) = ⊕_n B_Ω ⊗ L(E_d)_n` is `Z`-graded, with
   `H_0 = B_Ω ⊗ L(E_d)_0`. The identification `L_∂ ≅ L(E_d)` is
   `boundary-crossed-product-is-a-leavitt-path-algebra`. A corner `eHe` with
   `deg e = 0` is graded, with unit `e` and core `e H_0 e`.
2. **Homogeneous units form a group.** By step (A1) of
   `algebraic-core-gradings-bound-homogeneous-laurent-rank-proof`, the inverse of a
   homogeneous unit is homogeneous. A product of homogeneous units is a nonzero
   homogeneous element. So `G_h = {g ∈ Z^4 : φ(g) homogeneous}` is a subgroup, and
   `deg ∘ φ : G_h -> Z` is a homomorphism.
3. **Kernel rank.** Suppose `rank G_h = 4`.
   - The kernel `Λ` of the degree map has rank `>= 3`. Pick independent
     `n^(1), n^(2), n^(3) ∈ Λ`.
   - The monomials `t^{n^(j)}` are algebraically independent in `F[Z^4]`, since
     distinct exponent vectors `Σ a_j n^(j)` give distinct group elements.
   - `φ` is injective, so `w_j = φ(t^{n^(j)})` are three commuting algebraically
     independent elements of `e H_0 e`.
   - That contradicts (B3)–(B4). So `rank G_h <= 3`. ∎(C)
4. **General form.** Let the grading group `Γ'` have torsion-free rank `r`, and let
   `u_1, …, u_m` be homogeneous commuting units with `m > r + s`.
   - The kernel of `Z^m -> Γ'` has finite index in the kernel of `Z^m -> Γ' ⊗ Q`,
     which has rank `>= m - r >= s + 1`.
   - Steps 2–3 then apply verbatim, with (B2) for the core `B ⊗ L_0`. ∎

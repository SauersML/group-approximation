---
rg: 2
id: bernoulli-algebraic-idempotent-traces-reduce-to-the-host-proof
kind: route
title: Algebraic diagonals are window functions, orbit sums of window functions are pattern counts, and unitriangularity of counts turns equal ranks into equal traces for every invariant measure
target: bernoulli-algebraic-idempotent-traces-reduce-to-the-host
requires:
  - bernoulli-assembly-injective-beyond-the-host
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
---

Notation as in `bernoulli-algebraic-idempotent-traces-reduce-to-the-host`. RF = `bernoulli-assembly-injective-beyond-the-host`,
CC = `bernoulli-bc-splits-into-host-and-cylinder-comparison`.

## 0. Conventions

- `(g·x)(v) = x(g^(-1) v)`. For `z ∈ X`, `π_z` acts on `l^2(G) ⊗ C^k` by `π_z(f) δ_h = f(h·z) δ_h` and
  `π_z(u_g) δ_h = δ_(gh)`. Then `⟨π_z(f u_g) δ_(h'), δ_h⟩ = f(h·z)` if `h = g h'` and `0` otherwise, and the diagonal
  block is `⟨π_z(b) δ_h, δ_h⟩ = E(b)(h·z)`. This is RF item 1's orbit representation `Ind_({e})^G(ev_z)`.
- A **pattern** is `t = (T, a)` with `T ⊆ G` finite nonempty and `a : T -> Λ \ {0}`; `C_t = {x : x|_T = a}`; `x_t` is
  `a` on `T` and `0` elsewhere. `G` acts on patterns by translation, freely since `G` is torsion-free.
- For finite-support `x` and a pattern orbit `[s]`, `c_x([s]) = #{h ∈ G : h·x ∈ C_s}`. It depends only on `[s]`, and
  it is the number of occurrences `t <= x` with `t ∈ [s]` (free action). RF item 1: `r_x[1_(C_s)] = c_x([s])`. RF item 3
  defines `n(y)` by Möbius inversion, `r_x(y) = Σ_(t <= x) n_([t])(y) = Σ_([s]) n_([s])(y) c_x([s])` for every
  finite-support `x`.

## 1. Exact window (item 1)

- `e = Σ_(g ∈ S) f_g u_g` with `S` finite and `f_g ∈ M_k(C_lc(X))`. Choose finite `W ∋ e` such that every `f_g` depends
  only on `x|_W`.
- `E(e) = f_e` and `E(s(e_0)) = f_e(0)`, a constant matrix, because `(ev_0 ⋊ G)(e) = Σ_g f_g(0) u_g`.
- So `F(x) = tr f_e(x) - tr f_e(0)` depends only on `x|_W`, and `F(0) = 0`.

## 2. Pattern decomposition of a window function

**Lemma 2.1.** Every `F : X -> C` depending only on `x|_W`, with `F(0) = 0`, is uniquely
`F = Σ_(t ⊆ W) κ(t) 1_(C_t)`, the sum over patterns with support in `W`.

*Proof.* Both sides live in the space of functions on `Λ^W` vanishing at `0`, of dimension `|Λ|^|W| - 1`. The number
of patterns with support in `W` is `Σ_(∅ ≠ T ⊆ W) (|Λ| - 1)^|T| = |Λ|^|W| - 1`. The matrix
`(1_(C_t)(x_(t')))` is unitriangular for the order `t <= t'` (`1_(C_t)(x_(t')) = 1` iff `t <= x_(t')`), so the
indicators are independent, hence a basis. ∎

**Lemma 2.2 (orbit sums are counts).** For finite-support `x`, `Σ_(h ∈ G) F(h·x) = Σ_([s]) K([s]) c_x([s])`, with
`K([s]) = Σ_(t ⊆ W, t ∈ [s]) κ(t)`. The sum over `h` has finitely many nonzero terms.

*Proof.* `F(h·x) ≠ 0` needs `(h·x)|_W ≠ 0`, that is `h^(-1) W ∩ supp x ≠ ∅`: finitely many `h`. Then
`Σ_h F(h·x) = Σ_t κ(t) #{h : h·x ∈ C_t} = Σ_t κ(t) c_x([t])`. Group by orbits. ∎

**Lemma 2.3 (integrals are counts).** For every invariant probability `ν`,
`∫ F dν = Σ_t κ(t) ν(C_t) = Σ_([s]) K([s]) ν(C_s)`, because `ν(C_t)` depends only on `[t]`. ∎

## 3. Orbit sums are ranks

- `y = [e] - [s(e_0)]` lies in `K_0(C_0(X \ {0}) ⋊_r G)`: the quotient `ev_0 ⋊ G` of `C(X) ⋊_r G` onto `C*_r G` is
  split by `s ⋊ G`, so by split exactness `K_0` of the ideal is the kernel of `(ev_0 ⋊ G)_*`, and `y` maps to
  `[e_0] - [e_0] = 0`.
- Fix finite-support `x`. `D_x = π_x(e) - π_x(s(e_0)) = π_x(Σ_g (f_g - f_g(0)) u_g)`. The entry at `(h, h')` is
  `(f_g - f_g(0))(h·x)` with `h = gh'`. It vanishes unless `(h·x)|_W ≠ 0` and `h' ∈ S^(-1) h`. So `D_x` is supported on a
  finite block `R × S^(-1)R`, and it has finite rank.
- Context import: for idempotents `P, Q ∈ M_k(B(l^2))` with `P - Q` of finite rank, `[P] - [Q] ∈ K_0(K)` corresponds to
  `Tr(P - Q) ∈ Z` (the Fredholm index of `QP : ran P -> ran Q`).
- `π_x` maps the ideal into the compact operators (RF item 1), so `r_x(y) = K_0(π_x)(y) = Tr D_x`.
- An operator supported on a finite block has trace equal to the sum of its diagonal entries. By §0,
  `Tr D_x = Σ_h tr(f_e(h·x) - f_e(0)) = Σ_h F(h·x)`.

So `r_x(y) = Σ_([s]) K([s]) c_x([s])` for every finite-support `x`.

## 4. Proof of items 2--5

- **Item 2.** `K` is supported on the finitely many orbits meeting patterns in `W`. By uniqueness of the Möbius
  expansion (RF item 3; the count functions `c_x([s])` are unitriangular at `x = x_s` ordered by size, with value `1` at
  `[s]` itself by freeness), `n(y) = K`. Then `τ_ν(y) = τ_ν(e) - τ_ν(s(e_0)) = ∫ F dν = Σ n_([s])(y) ν(C_s)` by
  Lemma 2.3, and `τ_ν(T_r(n(y))) = Σ n_([s]) τ_ν(1_(C_s)) = Σ n_([s]) ν(C_s)`.
- **Item 3.** `τ(s(e_0)) = ∫ tr f_e(0) dμ = tr (e_0)_e = τ_G(e_0)`. For Haar `μ`, `μ(C_s) = p^(-|F_s|)`. Add item 2.
- **Item 4.** `=>`: `C[G] ⊆ C[H]` and `τ_H|_(C[G]) = τ_G`. `<=`: item 3, since `Σ n p^(-|F_s|) ∈ Z[1/p]`.
- **Item 5.** Ranks vanish iff `n(y) = 0`; then item 2 gives `τ_ν(y) = 0`. ∎

## 5. Where the argument stops for C*-classes

- For a projection `P ∈ M_k(C(X) ⋊_r G)`, `F = tr E(P) - tr E(P)(0)` is continuous but not a window function.
- Approximating `F` by window functions `F_W` with `||F - F_W||_∞ -> 0` keeps Lemma 2.3 but spoils §3: the orbit sums
  `Σ_h (F - F_W)(h·x)` have `~ |supp x| · #{h : d(h, supp x) <= R}` terms at scale `R`.
- They tend to `0` only if the decay of `F - F_W` beats the growth of balls. Combes--Thomas decay rates of gapped
  resolvents are not tied to the host's growth, so on exponential-growth hosts the step is not available. This is
  where a non-algebraic trace witness must live.

## 6. Calibration

- Cylinder `q = 1_(C_s)`: `W = F_s`, `κ = δ_s`, `n = δ_([s])`, `τ = p^(-|F_s|)`.
- Idempotent `q + q b (1 - q)` with `b = f u_g`, `g ≠ e`: `E(q b (1 - q)) = 0`, so `F = 1_(C_s)`, same answer; ranks of
  the two idempotents agree since they are similar in the algebra.
- `G = Z`, `p = 2`: every class of the ideal is a cylinder combination (Pimsner--Voiculescu, CC model test), so item 2
  is consistent there.
- Torsion is used only through freeness of the pattern action, which makes `c_x([s])` unitriangular; with torsion the
  stabilizers `G_s` enter as in RF's second artifact and item 2 would need representation-ring coefficients.

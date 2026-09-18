---
rg: 2
id: crossed-product-growth-bounded-by-ball-patterns-proof
kind: route
title: Every product of n local monomials is a combination of ball-cylinder monomials of radius mn + r; group elements are independent, and the permutation representation separates them when fixed sets are meagre
target: crossed-product-growth-bounded-by-ball-patterns
requires: []
---

Notation as in the target. `B = LC(X, k) ⋊ P` is the free left `LC(X, k)`-module on `{v_p}` with
`v_p v_q = v_(pq)` and `v_p f = (p·f) v_p`, where `(p·f)(x) = f(p^(-1) x)`. For finite `F ⊆ P` and
`w ∈ L_F(X)` put `[w] = { x ∈ X : x|_F = w }`, a nonempty clopen set.

## Part 1

**Step 0 (locality).** A function `f ∈ LC(X, k)` takes finitely many values on clopen level sets. The
cylinders `[w]`, `w ∈ L_(B_P(R))(X)`, over `R >= 0` form a base of clopen sets, and the partition at radius `R'`
refines the one at `R <= R'`. By compactness each level set is a finite union of cylinders, so `f` is constant
on the cylinders of some radius `R_f`. Call `f` *`R`-local* if `f(x)` depends only on `x|_(B_P(R))`. An
`R`-local function lies in `span{ χ_[w] : w ∈ L_(B_P(R))(X) }`, and it is `R'`-local for `R' >= R`.

**Step 1 (constants).** Write each `a ∈ S` as `a = Σ_(p ∈ supp a) f_(a,p) v_p`, a finite sum. Let `m` be the
largest `|p|` over all these supports (`m = 0` if all are `e`), and let `r` be such that every `f_(a,p)` is
`r`-local.

**Step 2 (the spaces).** For `N, R >= 0` put

`E(N, R) = span_k { χ_[w] v_p : |p| <= N, w ∈ L_(B_P(R))(X) }`,

so `dim E(N, R) <= |B_P(N)| · |L_(B_P(R))(X)|`, and `E(N, R) ⊆ E(N', R')` for `N <= N'`, `R <= R'`.

**Step 3 (translation moves locality).** If `f` is `r`-local and `|p| <= N`, then `p·f` is `(N + r)`-local.
Indeed `(p·f)(x) = f(p^(-1) x)` depends on `(p^(-1) x)|_(B_P(r))`, and `(p^(-1) x)(q) = x(pq)`. So it depends on
`x|_(p B_P(r))`, and `p B_P(r) ⊆ B_P(|p| + r) ⊆ B_P(N + r)`.

**Step 4 (induction).** Claim: every product of at most `n` elements of `S` lies in `E(mn, mn + r)`.
- For `n = 0`, `1 = Σ_(w ∈ L_(B_P(r))(X)) χ_[w] v_e ∈ E(0, r)`.
- For the step, take `χ_[w] v_p ∈ E(mn, mn + r)` and a term `f v_q` of some `a ∈ S`. Then
  `χ_[w] v_p f v_q = χ_[w] (p·f) v_(pq)`. Here `χ_[w]` is `(mn + r)`-local and `p·f` is `(mn + r)`-local by
  Step 3, so their product is a combination of `χ_[w']` with `w' ∈ L_(B_P(mn + r))(X)`. Also
  `|pq| <= mn + m`. Hence the product lies in `E(m(n+1), mn + r) ⊆ E(m(n+1), m(n+1) + r)`, and by linearity so
  does every product of at most `n + 1` elements. (Products of length `< n+1` are covered by monotonicity.)

So `B_(<= n) ⊆ E(mn, mn + r)`, which is part 1.

## Part 2

Since `k[G] ≠ 0` injects, `B ≠ 0`, so `X ≠ ∅` and every `|L_F(X)| >= 1`. The bound at `n = 0` is then trivial.

Put `S = { φ(t) : t ∈ T } ∪ { φ(e) }` and take `m, r` from part 1. Let `n >= 1`. Then `φ(e) ∈ S` is a
product of length `1 <= n`, and every `g ∈ B_G(n) ∖ {e}` is a product of between 1 and `n` elements of `T`.
So `φ(B_G(n)) ⊆ B_(<= n)`. The group elements are linearly independent in `k[G]` and `φ` is injective, so the
`φ(g)`, `g ∈ B_G(n)`, are linearly independent. Hence `|B_G(n)| <= dim B_(<= n)`, and part 1 gives part 2.

## Part 3

**Uniqueness of cocycles.** Let `c, c'` both satisfy `g(x) = c(x)·x`. The set `D = { c ≠ c' }` is clopen,
because both are locally constant. Each `x ∈ D` is fixed by `c'(x)^(-1) c(x) ≠ e`. The images of `c, c'` are
finite, so `D` lies in a finite union of sets `Fix(q)`, `q ≠ e`. These are closed with empty interior, by
topological freeness, and a finite union of closed nowhere dense sets is nowhere dense. So the open set `D` is
empty.

**The representation.** Define `π : B -> End_k(LC(X, k))` by `π(f v_p) ξ = f · (ξ∘p^(-1))`. It respects the
covariance relation: `π(v_p) π(f) ξ = (f ξ)∘p^(-1) = (p·f)(ξ∘p^(-1)) = π(p·f) π(v_p) ξ`, and
`π(v_p v_q) = π(v_p) π(v_q)`. So `π` is an algebra homomorphism by the universal property of the crossed product.

**The units.** For `g ∈ F(P ⋉ X)` put `U_p = { y : c_g(g^(-1) y) = p }`, a finite clopen partition of `X`. If
`y = g(x)` then `y = c_g(x)·x`, so `g^(-1) y = p^(-1) y` on `U_p`. Put `u_g = Σ_p χ_(U_p) v_p`. Then:
- `π(u_g) ξ = ξ∘g^(-1)`.
- **Multiplicativity.** Let `V_q` be the partition for `h`. Then
  `u_g u_h = Σ_(p,q) χ_(U_p) χ_(p V_q) v_(pq)`, because `p·χ_(V_q) = χ_(p V_q)`. For `y ∈ U_p ∩ p V_q`,
  `(gh)^(-1) y = h^(-1)(p^(-1) y) = q^(-1) p^(-1) y`. So `s |-> W_s = ⋃_(pq = s) (U_p ∩ p V_q)` is a clopen
  partition with `(gh)^(-1) = s^(-1)` on `W_s`, and `u_g u_h = Σ_s χ_(W_s) v_s`.
  - The function `x |-> s` for `gh(x) ∈ W_s` is a locally constant cocycle for `gh`. By uniqueness it is
    `c_(gh)`, so `W_s` is the partition for `gh`, and `u_g u_h = u_(gh)`.
  - Also `u_e = v_e = 1`. So `g |-> u_g` is a homomorphism into `B^x`.

**Injectivity.** Suppose `Σ_(i=1..n) c_i u_(g_i) = 0` with distinct `g_i ∈ G` and all `c_i ≠ 0`, `n >= 1`.
- For `i ≠ j`, `g_i^(-1) y = g_j^(-1) y` iff `y ∈ Fix(g_j g_i^(-1))`. By hypothesis this is closed with empty
  interior. The finite union over `i ≠ j` is nowhere dense, so some `y` lies outside it. The points
  `z_i = g_i^(-1) y` are then distinct.
- `X` is totally disconnected compact Hausdorff, so there is a clopen `W` containing `z_1` and none of
  `z_2, …, z_n`.
- Then `0 = (π(Σ c_i u_(g_i)) χ_W)(y) = Σ c_i χ_W(g_i^(-1) y) = c_1`, a contradiction.

**Calibration.** Let `g, h ∈ F(P ⋉ X)` have cocycles equal to `e` off disjoint clopen sets `S` and `T`. Then
`gh = hg`. The cocycle of `gh` is that of `g` on `S`, that of `h` on `T`, and `e` elsewhere. Writing
`u_g = χ_(X∖S) + a` and `u_h = χ_(X∖T) + b` with `a` supported in `S` and `b` in `T`,
`u_(gh) = χ_(X∖(S∪T)) + a + b`. So `1 - u_g - u_h + u_(gh) = 1 - χ_(X∖S) - χ_(X∖T) + χ_(X∖(S∪T)) = 0`, since
`S ∩ T = ∅`. That is, `(1 - u_g)(1 - u_h) = 0`, so `k[G] -> B` is not injective for `G = ⟨g, h⟩` whenever
`g ≠ e ≠ h`.

## Remark (general spaces)

If `X` is any compact totally disconnected `P`-space and `S` is finite, the finitely many coefficients `f_(a,p)`
separate a finite clopen partition `Q`. Put `Y` as the image of `x |-> (q |-> the atom of Q containing
q^(-1) x)` in `Q^P`. This is a subshift factor, and `LC(Y, k) ⋊ P ⊆ B` contains `S`. Apply part 1 there.

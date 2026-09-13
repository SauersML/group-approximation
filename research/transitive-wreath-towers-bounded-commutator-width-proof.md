---
rg: 2
id: transitive-wreath-towers-bounded-commutator-width-proof
kind: route
title: Lift the top commutators, move the base mass to one coordinate along a spanning tree, and absorb three commutators of H per two commutators of W at an adjacent pair of coordinates
target: transitive-wreath-towers-bounded-commutator-width
requires: []
---

Conventions: `(f; p)(g; s) = (f p(g); ps)`, `p(g)_i = g_(p^-1 i)`, `[x, y] = x y x^-1 y^-1`. Coordinatewise
products in `H^m` are written by juxtaposition.

## 1. Base lemma

For `x = (u; 1)`, `y = (q; beta)`, the commutator is `(f; 1)` with `f_i = u_i q_i u_(beta^-1 i)^-1 q_i^-1`.
- **Solving along a cycle.** Put `g_i = f_i q_i`. The equations say `u_i = g_i u_(beta^-1 i) q_i^-1`. Along a
  cycle `i_1, i_2 = beta(i_1), ..., i_L`, going once around gives
  `u_(i_1) = G u_(i_1) V^-1`, with `G = g_(i_1) g_(i_L) ... g_(i_2)` and `V = q_(i_1) q_(i_L) ... q_(i_2)`.
- **Solvability.** Conversely, if `G = s V s^-1`, put `u_(i_1) = s` and define the rest by the recursion. So the
  system is solvable iff `G ~ V` on every cycle.
- **Choice of `q`.** On each cycle take `q` supported at `i_1`, with `q_(i_1) = s`. Then `V = s`, and
  `G = f_(i_1) s f_(i_L) ... f_(i_2)` is conjugate to `F s` with `F = f_(i_L) ... f_(i_2) f_(i_1)`.
- **Conclusion.** `F s ~ s` iff `F = t s t^-1 s^-1` for some `t`. So if each `F` is a commutator `[t, s]`, choosing
  this `s` works. A fixed point is a cycle with `L = 1`, where the equation is `f_i = [u_i, q_i]`. The
  cycles are independent.

**Moves.** If `j` is not fixed by `beta` and `y in H`, the vector `(y at j, y^-1 at beta(j))` has ordered
product `y^-1 y = 1` on its cycle, and `1` on the others. So it is a commutator of `W`.

## 2. Three-for-two absorption

Let `i = beta(j_0) != j_0`. For `A, B in H`, the vector `(A at j_0, B at i)` has ordered product `B A` on the
cycle through `j_0`, so it is a commutator of `W` whenever `B A` is a commutator. The vector
`(mu at j_0, nu at i)` with commutators `mu, nu` is the commutator `[(k at j_0, k' at i; 1), (l at j_0, l' at i; 1)]`.
- **The blocks.** Given commutators `lambda_k, mu_k, nu_k`, `k = 1..N`, put `A_k = 1` for `k < N`, `B_k = lambda_k A_k^-1`,
  and `A_N = nu_N Pi lambda_N` with `Pi = lambda_1 nu_1 ... lambda_(N-1) nu_(N-1)`.
- **The product.** Put `g_k = (A_k at j_0, B_k at i)` and `h_k = (mu_k at j_0, nu_k at i)`. The coordinatewise product
  `g_1 h_1 ... g_N h_N` has:
  - at `i`: `lambda_1 nu_1 ... lambda_(N-1) nu_(N-1) · lambda_N A_N^-1 nu_N = Pi · lambda_N lambda_N^-1 Pi^-1 nu_N^-1 nu_N = 1`;
  - at `j_0`: `mu_1 ... mu_(N-1) · A_N mu_N = mu_1 ... mu_(N-1) nu_N lambda_1 nu_1 ... lambda_(N-1) nu_(N-1) lambda_N mu_N`.
- **Conclusion.** The last word is a product of `3N` free commutators in a fixed order. Assigning the
  commutator factors of `z` to them in that order gives `(z at j_0; 1)` as a product of `2N` commutators of
  `W`.

## 3. Inheritance

Let `x = (f; tau) in [W, W]`.
- **Constraints on `x`.** `(f; p) -> (f_1 ... f_m mod [H, H], p mod [T, T])` is a homomorphism to
  `H^ab × T^ab`, so `tau in [T, T]` and `f_1 ... f_m in [H, H]`.
- **The top.** `tau` is a product of at most `|T|` commutators of `T`: the commutator set contains `1`, so
  its powers increase to `[T, T]`. Lifting them as `(1; alpha)` gives `x = (f; 1) · prod [(1; alpha_k), (1; beta_k)]`.
- **Moves.** Fix a spanning tree of the graph on `[m]` with edges `{j, beta(j)}`, `beta in T`, and root `j_0`. It is
  connected because `T` is transitive. Stripping leaves, with one move per edge (`m - 1` commutators),
  solves `f = M_1 ... M_(m-1) · (P' at j_0)`. At a leaf `j` the only unsolved move is on its edge, and the move's
  entry there is `y` or `y^-1`, so it can be matched.
- **The defect.** Each move has product `1` modulo `[H, H]`, so `P' in [H, H]`.
- **Absorption.** Write `P'` as a product of `c_H` commutators, padded with `1` to `3 ceil(c_H/3)`. By Section 2,
  `(P' at j_0; 1)` is a product of `2 ceil(c_H/3)` commutators.
- **Total.** `|T| + (m - 1) + 2 ceil(c_H / 3)`.

## 4. The tower bound

Induct on depth, with `C = 3(m! + m + 2)`.
- *Depth one.* `W = T_1`, and `c <= |T_1| <= m! <= C`.
- *Step.* `W = H wr T_1`, with `H` a tower of smaller depth, so `c_H <= C`. Then
  `c_W <= m! + (m - 1) + 2(C/3 + 1) = m! + m + 1 + 2C/3 <= C`, since `C/3 = m! + m + 2`.
- *Trivial levels.* If some `m_i = 1`, that level is trivial and can be removed.

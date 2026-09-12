---
rg: 2
id: unital-limits-k1-injective-proof
kind: route
title: Detect the null-homotopy at a finite stage by a chain of close unitaries
target: unital-limits-of-k1-injective-algebras-are-k1-injective
requires: []
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Identify each `A_j` with its image in `A`; the union is dense. Let
`u in U(A)` with `[u] = 0` in `K_1(A)`.

1. Choose `i` and `u_i in U(A_i)` with `||u - u_i|| < 1`. Then
   `u_i u^*` has no `-1` in its spectrum, so its principal logarithm joins
   `u` to `u_i` in `U(A)`. It suffices to show `u_i in U_0(A)`, and
   `[u_i] = [u] = 0` in `K_1(A)`.
2. There is `n` and a path `w: [0,1] -> U(M_(n+1)(A))` from `u_i ⊕ 1_n` to `1`.
   By uniform continuity pick `0 = t_0 < ... < t_N = 1` with
   `||w(t) - w(t_k)|| < 1/8` on `[t_k, t_(k+1)]`.
3. Density of the matrix union gives `j >= i` and `x_k in M_(n+1)(A_j)` with
   `||x_k - w(t_k)|| < 1/16`. Then `||x_k^* x_k - 1|| < 0.13`, so `x_k` is
   invertible, and its polar unitary `v_k` satisfies
   `||v_k - w(t_k)|| <= ||x_k|| ||1 - |x_k|^(-1)|| + 1/16 < 1/4`. Put
   `v_0 = u_i ⊕ 1_n` and `v_N = 1`, which already lie in stage `j`.
4. Then `||v_k - v_(k+1)|| < 1/4 + 1/8 + 1/4 < 2`, so `v_k^* v_(k+1)` has no
   `-1` in its spectrum and `v_k exp(t log(v_k^* v_(k+1)))` is a path in
   `U(M_(n+1)(A_j))`. Concatenating gives `u_i ⊕ 1_n in U_0(M_(n+1)(A_j))`, and
   the same holds at every later stage.
5. Pick a later K1-injective stage `j'`. The class of `u_i` in `K_1(A_(j'))`
   is zero, so `u_i in U_0(A_(j'))`, and hence `u_i in U_0(A)`. Square.

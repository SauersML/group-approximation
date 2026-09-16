---
rg: 2
id: cnd-support-shift-actions-are-a-t-menable-proof
kind: route
title: A locally constant support basepoint turns CND supports into a locally proper negative-type function on the shift groupoid
target: cnd-support-shift-actions-are-a-t-menable
requires: []
artifacts:
  - research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md
---

Complete elementary proof. The same text, with remarks, is Section 3 of
`research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`. Notation is that of the target. Write `|g| = d(e, g)`,
and note `supp(g·x) = g supp x`, so `supp(xg) = g^(-1) supp x`.

**Step 1: `T_cnd` is closed, invariant and hereditary.**
- Hereditary: immediate from the definition.
- Invariant: `d(gu, gv) = d(u, v)`, so `d` restricted to `gF` is CND iff `d` restricted to `F` is.
- Closed: let `x_k -> x` with `x_k ∈ T_cnd`, and let `F ⊆ supp x` be finite. The topology is pointwise and `Λ` is finite,
  so `x_k|_F = x|_F` for large `k`. Then `F ⊆ supp x_k`, so `d` restricted to `F` is CND.

**Step 2: a continuous basepoint.**
- Enumerate `G = {h_1, h_2, ...}` and put `U_k = {x ∈ X : x(h_k) ≠ 0 and x(h_j) = 0 for all j < k}`.
- Each `U_k` is clopen. The `U_k` are pairwise disjoint, and their union is `X^0`.
- Put `a_0 = h_k` on `U_k`. So `a_0 : X^0 -> G` is locally constant, and `a_0(x) ∈ supp x`.

**Step 3: the function.**
- For `x ∈ Z` and `g ∈ G` put `h(x, g) = d(g^(-1) a_0(x), a_0(xg))`.
- For fixed `g`, `x ↦ xg` is continuous and `a_0` is locally constant. `G` is discrete, so `h` is locally constant on
  `Z × G`, hence continuous.

**Step 4: conditions 1 and 2.**
- `h(x, e) = d(a_0(x), a_0(x)) = 0`.
- `h(xg, g^(-1)) = d(g a_0(xg), a_0(x))`. Multiplying both arguments on the left by `g^(-1)` gives
  `d(a_0(xg), g^(-1) a_0(x)) = h(x, g)`.

**Step 5: condition 3.**
- Fix `x ∈ Z`, `g_1, ..., g_n ∈ G` and real `t_i` with `Σ t_i = 0`. Put `p_i = g_i a_0(x g_i)`.
- Multiplying both arguments on the left by `g_j`:

  ```text
  h(x g_i, g_i^(-1) g_j) = d( g_j^(-1) g_i a_0(x g_i), a_0(x g_j) ) = d(p_i, p_j).
  ```

- `a_0(x g_i) ∈ supp(x g_i) = g_i^(-1) supp x`, so `p_i ∈ supp x`.
- Group equal `p_i` and add their coefficients. The new coefficients still sum to `0`, and the quadratic form is
  unchanged. `d` restricted to the finite set `{p_1, ..., p_n} ⊆ supp x` is CND because `x ∈ T_cnd`, so
  `Σ t_i t_j h(x g_i, g_i^(-1) g_j) <= 0`.

**Step 6: condition 4.**
- Let `K ⊆ Z` be compact. The open sets `U_k` cover `K`, so `K ⊆ U_1 ∪ ... ∪ U_m` for some `m`, and
  `a_0(K) ⊆ {h_1, ..., h_m}`. Put `M = max_(k <= m) |h_k|`.
- Let `x ∈ K` and `xg ∈ K`, with `a = a_0(x)` and `b = a_0(xg)`. By the triangle inequality and left invariance,

  ```text
  h(x, g) = d(g^(-1) a, b) >= d(g^(-1), e) - d(g^(-1) a, g^(-1)) - d(b, e) = |g| - |a| - |b| >= |g| - 2M.
  ```

- So for `R >= 0`, the set `{(x, g) : x ∈ K, xg ∈ K, h(x, g) <= R}` lies in `K × {g : |g| <= R + 2M}`. That set is
  compact, because word-metric balls are finite.
- The set on the left is closed in `Z × G`, because `h` and `(x, g) ↦ xg` are continuous and `K` is closed. So it is
  compact, which is properness of `h` on `{(x, g) : x ∈ K, xg ∈ K}`.

Steps 1 and 3--6 prove items 1 and 2 of the target. QED.

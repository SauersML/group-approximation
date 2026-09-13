---
rg: 2
id: bs12-logarithmic-table-length-proof
kind: route
title: Table length is subadditive under composition and invariant under inversion, and Horner's rule writes g^N as g^b f g^N' f^-1 with N' ≈ N/l, so L(g^N) grows logarithmically
target: bs12-images-in-nv-have-logarithmic-table-length
requires: []
---

Notation as in the target.

**Step 1 (inversion).** Swapping the two sides of every pair in a table of `a`
gives a table of `a^-1` with the same side lengths. So `L(a^-1) = L(a)`.

**Step 2 (subadditivity: `L(ab) ≤ L(a) + L(b)`).**
- Fix tables `A_i → A'_i` of `a` and `B_k → B'_k` of `b`, with all sides of
  length at most `L(a)` and `L(b)` respectively.
- **Intersections.** Two bricks meet iff their sides are prefix-comparable in
  every coordinate, and then their intersection is the brick whose `j`-th side
  is the longer of the two `j`-th sides.
- For each pair `(i, k)` with `A_i ∩ B'_k ≠ ∅`, write the `j`-th side of
  `A_i ∩ B'_k` as `β_j t_j = α_j s_j`. Here `β_j` and `α_j` are the `j`-th sides
  of `B'_k` and `A_i`, and exactly one of `t_j`, `s_j` is nonempty unless
  `α_j = β_j`. So `|t_j| ≤ |α_j| ≤ L(a)` and `|s_j| ≤ |β_j| ≤ L(b)`.
- **The composite on a piece.** `b^-1` maps `A_i ∩ B'_k` onto the brick with
  sides `γ_j t_j`, where `γ_j` is the `j`-th side of `B_k`. The map `ab` sends
  `γ_j t_j w_j ↦ β_j t_j w_j = α_j s_j w_j ↦ α'_j s_j w_j`, where `α'_j` is the
  `j`-th side of `A'_i`.
- **The table.** For fixed `k` the bricks `A_i ∩ B'_k` partition `B'_k`. So the
  bricks `b^-1(A_i ∩ B'_k)` partition `C^n`, and their images
  `a(A_i ∩ B'_k)` partition `C^n` as well. This is a table of `ab` with sides of
  length `|γ_j t_j| ≤ L(b) + L(a)` and `|α'_j s_j| ≤ L(a) + L(b)`.

**Step 3 (exponents are dominated by table length).**
- Refining a brick pair appends the same word to `u_j` and `v_j`, so `δ_h(x)`
  does not depend on the table. Any two tables have a common refinement, since
  the intersections of Step 2 are bricks.
- On a minimal table all sides have length at most `L(h)`, so
  `|δ_h(x)|_∞ ≤ L(h)`.
- It is enough to bound `L(g^N)`.

**Step 4 (reduction to `N ≥ 1` and `l ≥ 2`).**
- `L(g^-N) = L(g^N)` by Step 1.
- If `l ≤ -2`, then `f^2 g f^-2 = f g^l f^-1 = (f g f^-1)^l = g^{l^2}`, and
  `l^2 ≥ 4`. Replace `f` by `f^2` and `l` by `l^2`.

**Step 5 (Horner's rule).**
- **One step.** For `N ≥ 1`, let `b ∈ {0, …, l-1}` with `N ≡ b (mod l)`, and set
  `N' = (N - b)/l`, so `0 ≤ N' ≤ N/l`. Since `f g^{N'} f^-1 = (f g f^-1)^{N'}
  = g^{l N'}`, we have `g^N = g^b · f g^{N'} f^-1`.
- **The recursion.** By Steps 1 and 2,
  `L(g^N) ≤ b L(g) + 2 L(f) + L(g^{N'}) ≤ A + L(g^{N'})`, where
  `A = (l-1) L(g) + 2 L(f)`.
- **Iterating.** Starting from `N_0 = N` and setting `N_{t+1} = N_t'`, we get
  `N_t ≤ N / l^t`. So `N_t = 0` once `t > log_l N`, and `L(g^0) = L(id) = 0`.
- **Result.** `L(g^N) ≤ A (⌊log_l N⌋ + 1) ≤ A (1 + log_2 N)`.

With Step 4, `c = A` computed for the modified pair `(f, l)` works for all
`N ≠ 0`. By Step 3 the same `c` bounds `|δ_{g^N}(x)|_∞`. ∎

---
rg: 2
id: thompson-t-compression-one-half-via-cylinder-charts
kind: route
title: The standard-chart cocycle has square-root growth on T, and undistorted F caps the exponent
target: thompson-t-has-hilbert-space-compression-one-half
requires: [thompson-v-standard-cylinder-charts-are-commensurated, thompson-f-word-length-is-comparable-to-caret-count, thompson-f-has-hilbert-space-compression-one-half]
---

## Why sufficient

**Conventions.** Fix finite generating sets `S_F` of `F` and `S_T ⊇ S_F` of `T`.
Write `|·|_F`, `|·|_T` for word length and `d_T(g,h) = |g^{-1}h|_T`.

- `T` acts on `R/Z`. An element is a diagram `(S, R, k)`: `S` and `R` are binary
  trees with `n+1` leaves, and leaf interval `i` of `S` maps affinely onto leaf
  interval `i+k mod (n+1)` of `R`.
- `F` is the stabiliser of `0`, i.e. the elements with a diagram having `k = 0`.
- `T ⊂ V` via the Cantor set `C = {0,1}^N`. Cylinders `[w]` correspond to
  standard dyadic arcs. A diagram `(S, R, k)` is read as the tree pair `(S, R, σ)`
  with `σ(i) = i + k mod (n+1)`, where each leaf `[u]` of `S` goes to
  `[σ(u)]` of `R` by prefix replacement.

By Theorem 0 below, this identifies the caret counts, so `c(g)` denotes the
common caret count of the reduced diagram in `F`, `T` or `V`.

**Theorem 0 (one caret count on F ⊂ T ⊂ V).** The two caret counts agree on `T`
and on `F`.

1. A removable pair in the V pair `(S, R, σ)` means a caret of `S` with leaves
   `i, i+1` whose images `σ(i), σ(i+1)` are the left and right leaves of one
   caret of `R`. That is exactly a removable pair of the T diagram `(S, R, k)`,
   and of the F diagram when `k = 0`.
2. So a T-reduced diagram has no removable pair as a V pair.
3. A V pair `(S, R, σ)` with no removable pair has internal node set exactly
   `N_g`, in the notation of `thompson-v-standard-cylinder-charts-are-commensurated-proof`:
   - That proof shows the internal nodes `I` of `S` contain `N_g`.
   - Suppose `I ⊋ N_g`. Take `w ∈ I \ N_g` of maximal length. Children of
     canonical words are canonical, so `w0, w1 ∉ I`, and hence both are leaves
     of `S`.
   - `w` is canonical: `g` maps `wu ↦ w'u`. So `g` maps leaf `[w0]` onto `[w'0]`
     and leaf `[w1]` onto `[w'1]`.
   - Leaves of `S` go to leaves of `R`, so `w'0, w'1` are sibling leaves of `R`.
     That gives a removable pair, a contradiction.
4. Hence `c_F(f) = c_T(f) = c_V(f)` on `F`, `c_T = c_V` on `T`, and this is the
   quantity `c` in the chart claim.

**Step 1 (the cocycle).** Let `X` and `A` be as in
`thompson-v-standard-cylinder-charts-are-commensurated`, restrict the `V`-action
on `X` to `T`, and let `λ` be the permutation representation on `ℓ²(X)`.

- Put `b(g) = 1_{gA} - 1_A`. It is finitely supported, since `|gA Δ A| = 2c(g)`.
- `b(gh) = λ(g)b(h) + b(g)`. So `g·ξ = λ(g)ξ + b(g)` is an affine isometric
  action whose orbit map at `0` is `b`.
- `b(g) - b(h) = λ(h)(1_{h^{-1}gA} - 1_A)`, hence
  `‖b(g) - b(h)‖² = |h^{-1}gA Δ A| = 2c(h^{-1}g)`.

**Step 2 (subadditivity, Lipschitz bound).**
`|xyA Δ A| ≤ |xyA Δ xA| + |xA Δ A| = |yA Δ A| + |xA Δ A|` gives
`c(xy) ≤ c(x) + c(y)`. Also `|x^{-1}A Δ A| = |A Δ xA|` gives `c(x^{-1}) = c(x)`.
With `M = max_{s ∈ S_T} c(s)` this yields `c(x) ≤ M|x|_T`. So
`‖b(g) - b(h)‖ ≤ (2M d_T(g,h))^{1/2} ≤ (2M)^{1/2} d_T(g,h)` when `g ≠ h`, and `b` is
Lipschitz.

**Step 3 (word length in T is linear in carets).**
By `thompson-f-word-length-is-comparable-to-caret-count` there is `K_0` with
`|f|_F ≤ K_0(c(f) + 1)` on `F` (Theorem 0 identifies `N = c` on `F`). Put
`L = max_{s ∈ S_F} |s|_T`, so `|f|_T ≤ L|f|_F`. Let `g = (S, R, k)` be reduced with
`n = c(g)`.

- **Case `k = 0`.** Then `g ∈ F` and `|g|_T ≤ L K_0 (n+1)`.
- **Case `1 ≤ k ≤ n`.**
  - Let `P` be a tree with `n+1` leaves whose root has a left subtree with
    `n+1-k` leaves and a right subtree with `k` leaves. Let `P'` be `P` with the
    two root subtrees swapped. Let `ρ = R_{1/2}`.
  - `ρ` translates `[0,1/2]` onto `[1/2,1]` and back, so it maps leaf `i` of `P`
    to leaf `i + k mod (n+1)` of `P'`. So `ρ = (P, P', k)`.
  - Composing leafwise, `g = (P', R, 0) ∘ ρ ∘ (S, P, 0)`.
  - The outer factors `f_1 = (P', R, 0)` and `f_2 = (S, P, 0)` lie in `F`, and
    each is represented with `n` carets, so `c(f_i) ≤ n`.
  - Hence `|g|_T ≤ 2 L K_0 (n+1) + |ρ|_T`.

In both cases `|g|_T ≤ K(c(g) + 1)` with `K = 2LK_0 + |ρ|_T`.

**Step 4 (α*(T) ≥ 1/2).** Step 3 gives `c(x) ≥ |x|_T/K - 1`, so by Step 1
`‖b(g) - b(h)‖ = (2c(h^{-1}g))^{1/2} ≥ (max(0, 2d_T(g,h)/K - 2))^{1/2}`. Using
`√(u - v) ≥ √u - √v` for `u ≥ v ≥ 0` (and `0 ≥ √u - √v` otherwise), this is at
least `(2/K)^{1/2} d_T(g,h)^{1/2} - √2`. With Step 2, `b` is a Lipschitz orbit map of an
affine isometric action with exponent `1/2`. So
`α(T) ≥ α*(T) ≥ 1/2`.

**Step 5 (F is undistorted in T).** For `f ∈ F`,
`|f|_F ≤ K_0(c(f) + 1) ≤ K_0(M|f|_T + 1)` by Theorem 0 and Step 2, and
`|f|_T ≤ L|f|_F`. So `(F, d_F) → (T, d_T)` is a quasi-isometric embedding.

**Step 6 (α(T) ≤ 1/2).**

- Let `φ: T → H` be Lipschitz with `‖φ(x) - φ(y)‖ ≥ C d_T(x,y)^a - D`. Then
  `a ≤ 1`, because `φ` is Lipschitz and `T` is infinite.
- Restrict `φ` to `F`. The restriction is Lipschitz for `d_F`, since
  `d_T ≤ L d_F`.
- By Step 5, `d_T(x,y) ≥ (d_F(x,y) - K_0)/(K_0 M)`.
- `t ↦ t^a` is subadditive for `0 ≤ a ≤ 1`, so `(u - v)^a ≥ u^a - v^a` for
  `u ≥ v ≥ 0`. This gives
  `‖φ(x) - φ(y)‖ ≥ C (K_0 M)^{-a} d_F(x,y)^a - C (K_0 M)^{-a} K_0^a - D`. (When
  `d_F < K_0`, the right side is negative and the bound is trivial.)
- So `a ≤ α(F)`, and `α(F) = 1/2` by
  `thompson-f-has-hilbert-space-compression-one-half`.
- Taking the supremum, `α(T) ≤ 1/2`, and `α*(T) ≤ α(T)` always.

With Step 4, `α*(T) = α(T) = 1/2`. ∎

**Addendum used in the claim's remark (α*(F) = 1/2).** Restricting `b` to `F`
gives `‖b(f) - b(f')‖² = 2c(f^{-1}f') ≥ 2(|f^{-1}f'|_F/K_0 - 1)`. So `α*(F) ≥ 1/2`,
and `α*(F) ≤ α(F) = 1/2`.

**What this does not give.** Compression is a quasi-isometry invariant
(Guentner–Kaminker, arXiv:math/0309166, abstract), so `α(F) = α(T)` removes
compression as a separating invariant for Zaremsky Problem 2.4(c). It says
nothing for or against the target QI. `α*` is defined through the group action
and is not used here as a QI invariant, so `α*(F) = α*(T)` is recorded only as a
fact. The finer compression gap could still
differ in principle, but any upper bound for `F` transfers to `T` by Step 6, and
the lower bound `√t/C` holds for both.

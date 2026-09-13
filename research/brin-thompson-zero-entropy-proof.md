---
rg: 2
id: brin-thompson-zero-entropy-proof
kind: route
title: Table lengths bound the separation growth of nV elements, entropy is a conjugacy invariant that scales with powers, so a proper-power relation forces zero entropy; the baker map shifts digits and separates 2^N points
target: brin-thompson-proper-power-conjugates-have-zero-entropy
requires: []
---

Notation as in the target. Write `s_N(T,ε)` for the largest `(N,ε)`-separated
set. It does not decrease when `N` grows or `ε` shrinks.

**Step E0 (conjugacy invariance).**
- Let `S = f T f^-1`. Given `ε > 0`, uniform continuity of `f` gives `δ > 0`
  with `d(u,v) ≤ δ ⇒ d(fu, fv) ≤ ε`.
- If `E` is `(N,ε)`-separated for `S`, take `x ≠ y ∈ E` and `t < N` with
  `d(f T^t f^-1 x, f T^t f^-1 y) > ε`. Then `d(T^t f^-1 x, T^t f^-1 y) > δ`, so
  `f^-1 E` is `(N,δ)`-separated for `T`.
- Hence `s_N(S,ε) ≤ s_N(T,δ)` and `h(S) ≤ h(T)`. Exchanging `S` and `T` gives
  equality.

**Step E1 (finite entropy on nV).**
- **One step.** Let `L = L(g)`. If `m(x,y) ≥ L`, then `x` and `y` agree on all
  words of length `≤ L`, so they lie in the same domain brick `Π_j C(u_j)` of a
  table of `g`, mapped to `Π_j C(v_j)`. Writing `x_j = u_j w_j` and
  `y_j = u_j w'_j`, the tails `w_j, w'_j` share a prefix of length at least
  `m(x,y) - |u_j|`. So `(gx)_j = v_j w_j` and `(gy)_j = v_j w'_j` share a prefix
  of length at least `|v_j| + m(x,y) - |u_j| ≥ m(x,y) - L`. If `m(x,y) < L` the
  same inequality holds trivially. So `m(gx, gy) ≥ m(x,y) - L`, and by induction
  `m(g^t x, g^t y) ≥ m(x,y) - tL`.
- **Counting.** Let `ε = 2^(-r)` with `r ≥ 0` an integer, and let `E` be
  `(N,ε)`-separated for `g`. For `x ≠ y ∈ E` there is `t < N` with
  `m(g^t x, g^t y) < r`, so `m(x,y) < r + tL ≤ r + (N-1)L =: R`. Two points with
  the same prefixes of length `R` in every coordinate have `m ≥ R`, so sending a
  point to those prefixes is injective on `E`. Hence `|E| ≤ 2^(nR)`.
- **Limit.** `(1/N) log s_N(g, 2^(-r)) ≤ n (r + (N-1)L) log 2 / N → n L log 2`.
  Every `ε ∈ (0,1]` has `ε ≥ 2^(-r)` for some `r`, and `s_N` doesn't decrease as
  `ε` shrinks. So `h(g) ≤ n L log 2`.

**Step E2 (powers).** `T` is a homeomorphism of a compact metric space and
`k ≥ 1`.
- **`h(T^k) ≤ k h(T)`.** An `(N,ε)`-separated set for `T^k` is
  `(kN,ε)`-separated for `T`, because the times `tk` with `t < N` are below
  `kN`. So `s_N(T^k,ε) ≤ s_(kN)(T,ε)`, and
  `limsup_N (1/N) log s_N(T^k,ε) ≤ k · limsup_M (1/M) log s_M(T,ε)`.
- **`h(T^k) ≥ k h(T)`.**
  - Given `ε`, choose `δ ∈ (0,ε]` with `d(u,v) ≤ δ ⇒ d(T^j u, T^j v) ≤ ε` for
    `0 ≤ j < k`.
  - Let `E` be `(kN,ε)`-separated for `T`. For `x ≠ y ∈ E` there is `t < kN` with
    `d(T^t x, T^t y) > ε`. Write `t = qk + j` with `0 ≤ j < k` and `q < N`. If
    `d(T^(qk) x, T^(qk) y) ≤ δ`, then `d(T^t x, T^t y) ≤ ε`, a contradiction. So
    `E` is `(N,δ)`-separated for `T^k`, and `s_(kN)(T,ε) ≤ s_N(T^k,δ)`.
  - For `kN ≤ M < k(N+1)`: `s_M(T,ε) ≤ s_(N+1)(T^k,δ)`. So
    `limsup_M (1/M) log s_M(T,ε) ≤ (1/k) limsup_N (1/N) log s_N(T^k,δ)`.
  - As `ε → 0` we have `δ → 0`, so `h(T) ≤ h(T^k)/k`.
- **Inverse.**
  - Let `E` be `(N,ε)`-separated for `T^-1`, and set `F = T^(-(N-1)) E`. For
    `x ≠ y ∈ E` pick `t < N` with `d(T^(-t) x, T^(-t) y) > ε`.
  - With `x' = T^(-(N-1)) x` and `y' = T^(-(N-1)) y`, we get
    `T^(N-1-t) x' = T^(-t) x` and `T^(N-1-t) y' = T^(-t) y`, where
    `0 ≤ N-1-t < N`. So `F` is `(N,ε)`-separated for `T`, and `|F| = |E|`.
  - Hence `s_N(T^-1,ε) ≤ s_N(T,ε)`. By symmetry `h(T^-1) = h(T)`, and so
    `h(T^m) = |m| h(T)` for all `m ≠ 0`.

**Step E3 (proper powers).** From `f g^k f^-1 = g^l`, E0 and E2 give
`|l| h(g) = h(g^l) = h(f g^k f^-1) = h(g^k) = |k| h(g)`. So
`(|l| - |k|) h(g) = 0`, and `h(g) < ∞` by E1. Since `|k| ≠ |l|`, `h(g) = 0`.

**Step E4 (baker map).**
- **Table.** `b` has the table `C(0) × C → C × C(0)` and `C(1) × C → C × C(1)`,
  each by prefix replacement. So `b ∈ 2V`.
- **Separated set.** For a word `w ∈ {0,1}^N` put `p_w = (w 0^∞, 0^∞)`. The first
  coordinate of `b^t p_w` is the sequence `w 0^∞` shifted by `t`, so its first
  digit is `w_t` for `t < N`.
- If `w ≠ w'`, let `t` be the first index with `w_t ≠ w'_t`. Then `b^t p_w` and
  `b^t p_(w')` differ in the first digit of the first coordinate, so their
  distance is `1 > 1/2`.
- So `{p_w}` is `(N,1/2)`-separated, `s_N(b,1/2) ≥ 2^N`, and `h(b) ≥ log 2`.
  Item 4's non-relation follows from E3. ∎

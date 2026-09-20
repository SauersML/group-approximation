---
rg: 2
id: thompson-f-tower-size-laws-have-zero-defect-proof
kind: route
title: Dominant uniforms reduce interval sums to log-scales, a uniform height absorbs one log-scale, and the remaining gaps are the same problem one stage lower with one coordinate fewer
target: thompson-f-tower-size-laws-have-zero-defect
requires: []
artifacts:
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.py
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.out
---

Notation is as in `thompson-f-tower-size-laws-have-zero-defect`. `TV` is the total variation distance.
We use three standard facts.
- (T1) `TV(K P, K Q) <= TV(P, Q)` for a Markov kernel `K`, in particular for a measurable map.
- (T2) If `P = ∫ P_θ dπ(θ)` and `Q = ∫ Q_θ dπ(θ)` with the same mixing law `π`, then
  `TV(P, Q) <= ∫ TV(P_θ, Q_θ) dπ`.
- (T3) `TV(P ⊗ P', Q ⊗ Q') <= TV(P, Q) + TV(P', Q')`.

Also, the uniform law on `{0, ..., M − 1}` and its shift by an integer `E >= 0` are at distance
`min(1, E / M)`.

## Lemma B (one stage)

Consider one stage `(λ, g, u, n)` with parameters `R_0, R, G` on leaves `1..N'`, as defined in the claim.
Let `1 <= a_0 < a_1 < ... < a_k <= N'` be points and `J_0, ..., J_k` be intervals with:
- `J_i = [a_i, a_(i+1) − 1]` for `i < k`;
- `J_k` an interval starting at `a_k`, inside `[a_k, N']`.

Let `A = {a_0, ..., a_k}`, and let `E_0, ..., E_k` be random variables that are measurable with respect
to `(λ, g, (u_v)_(v ∉ A))` and satisfy

`0 <= E_j <= c + Σ_(v ∈ J_j, v ≠ a_j) n_v`.

Put `Y_j = n_(a_j) + E_j` and `F_i = Σ_(v ∈ J_i) g_v` for `i < k`. There is a Markov kernel `Φ_k`,
depending only on `k` (not on the points, the intervals or the `E_j`), such that

`TV( law (Y_j)_(j ≤ k),  Φ_k( law (F_i)_(i < k) ) ) <= (k + 1)(c 2^(−R_0) + 2^(2−G)) + E[D_1] / (R + 1)`.   (B)

For `k = 0` the right-hand kernel is the fixed law `Φ_0 = law of 2^Λ + U`, where `Λ` is uniform on
`{R_0..R_0+R}` and, given `Λ`, `U` is uniform on `{0..2^Λ − 1}`.

**Step (i): drop the garbage.** Put `M_j = 2^(λ + D_(a_j))` and `Y'_j = M_j + u_(a_j)`.
- Condition on `θ = (λ, g, (u_v)_(v ∉ A))`. The `u_(a_j)` are independent and uniform on
  `{0..M_j − 1}`, and the `E_j` are constants.
- So `(Y_j)` and `(Y'_j)` are products of shifted uniforms, and by (T3) their conditional distance is at
  most `Σ_j E_j / M_j`.
- For `v ∈ J_j` with `v > a_j`, we have `n_v < 2^(λ + D_v + 1)` and `D_v <= D_(a_j) − G (v − a_j)`. Hence
  `Σ_(v ∈ J_j, v > a_j) n_v / M_j < Σ_(t >= 1) 2^(1 − tG) <= 2^(2−G)`.
- Also `c / M_j <= c 2^(−R_0)`, since `λ >= R_0` and `D >= 0`.

By (T2), `TV(law Y, law Y') <= (k + 1)(c 2^(−R_0) + 2^(2−G))`.

**Step (ii): a fixed kernel on log-scales.** Put `x_j = λ + D_(a_j)`. Given `(λ, g)`, the `Y'_j` are
independent, and `Y'_j` is uniform on `[2^(x_j), 2^(x_j + 1))`. So `law Y' = K_k(law x)`, where `K_k` is the
product kernel `x ↦ ⊗_j Unif[2^(x_j), 2^(x_j+1))`. This kernel depends only on `k`.

**Step (iii): absorb one log-scale.** We have `F_i = D_(a_i) − D_(a_(i+1)) = x_i − x_(i+1)`, because `J_i`
is exactly `[a_i, a_(i+1) − 1]`. So `x = β(x_k, F)` with `β(y, F)_j = y + Σ_(j <= i < k) F_i`, a fixed
bijection.
- The variable `F` is a function of `g`, and `g` is independent of `λ`.
- Conditionally on `g`, `x_k = λ + D_(a_k)` is uniform on `{R_0 + D_(a_k), ..., R_0 + R + D_(a_k)}`. Its
  distance to `Unif{R_0..R_0+R}` is at most `D_(a_k) / (R + 1) <= D_1 / (R + 1)`.

By (T2), `TV( law (x_k, F), Unif{R_0..R_0+R} ⊗ law F ) <= E[D_1] / (R + 1)`.

Put `Φ_k(Q) = K_k β_*(Unif{R_0..R_0+R} ⊗ Q)`. This is a Markov kernel depending only on `k` and on
the stage parameters. By (T1), `TV(law Y', Φ_k(law F)) <= E[D_1] / (R + 1)`.

Adding steps (i) to (iii) gives (B). For `k = 0` there is no `F`, and step (iii) is the same statement
with `β(y) = y`. ∎

## The recursion (sizes)

Stage `t` has `N_t = N − t + 1` leaves, parameters `R_0^(t), R^(t), G_t`, and `k_t = w + 1 − t`. For
`t <= w` its gaps are `g^(t)_v = G_t + n^(t+1)_v` (`v = 1..N_t − 1 = N_(t+1)`), where stage `t + 1` is
independent of stage `t`'s own `λ` and `u`. Stage `w + 1` has constant gaps `G_(w+1)`. Every stage is
finitely supported. So `D^(t)_1` is bounded, and it depends on stages `> t` only.

Fix a cut `a` and an offset `b`. Define, for `t = 1, ..., w + 1`, the vector `V^(t)(a, b)` of length
`k_t + 1`:
- `V^(1)_j = b_j + Σ_(v ∈ I_j) n^(1)_v`, for `j = 0..w`;
- `V^(t+1)_i = Σ_(v ∈ I_i) g^(t)_v = G_t |I_i| + Σ_(v ∈ I_i) n^(t+1)_v`, for `i = 0..k_t − 1`.

These use the same intervals `I_0, ..., I_(k_t − 1)` of the cut. They are the gap sums `F` of stage `t`.

**Stage `t` is an instance of Lemma B**, with points `a_0..a_(k_t)`, `J_i = I_i` and garbage:
- for `t = 1`: `E_j = b_j + Σ_(v ∈ I_j, v ≠ a_j) n_v` and `c_1 = c`;
- for `t >= 2`: `E_i = G_(t−1) |I_i| + Σ_(v ∈ I_i, v ≠ a_i) n^(t)_v` and `c_t = G_(t−1) N`.

Two conditions have to be checked.
- *Measurability.* The garbage involves only the `u_v` with `v ∉ A`, together with `λ` and `g` of that
  stage.
- *Interval shape.* `J_i = [a_i, a_(i+1) − 1]` for `i < k_t`, and `J_(k_t) ⊆ [a_(k_t), N_t]`. At `t = 1` this
  holds because `J_w = I_w = [a_w, N]`. For `t >= 2`, `J_(k_t) = [a_(k_t), a_(k_t + 1) − 1]`, and
  `a_(k_t + 1) <= N − (w − k_t − 1) = N_t + 1`, because the cut points are strictly increasing and `a_w <= N`.

Write `ε_t` for the right side of (B) at stage `t`. Lemma B gives

`TV( law V^(t)(a, b),  Φ^(t)( law V^(t+1)(a, b) ) ) <= ε_t`   for `t <= w`,
`TV( law V^(w+1)(a, b),  Φ^(w+1)_0 ) <= ε_(w+1)`.

Here the kernels `Φ^(t)` and the fixed law `Φ^(w+1)_0` do not depend on `(a, b)`.

**Induction.** Let `Δ_t = sup TV(law V^(t)(a, b), law V^(t)(a', b'))` over all pairs of cuts and offsets.
By the triangle inequality and (T1),

`Δ_t <= 2 ε_t + Δ_(t+1)`,   `Δ_(w+1) <= 2 ε_(w+1)`,   so   `Δ_1 <= 2 Σ_(t = 1..w+1) ε_t`.

**Making it small.** `ε_t = (k_t + 1)(c_t 2^(−R_0^(t)) + 2^(2 − G_t)) + E[D^(t)_1] / (R^(t) + 1)`. Take the
parameters in the order of the claim:
1. all `G_t` with `2^(2−G_t) <= ε'`;
2. then all `R_0^(t)` with `c_t 2^(−R_0^(t)) <= ε'`, where `c_t` is known after step 1;
3. then `R^(w+1), R^(w), ..., R^(1)` in that order, with `E[D^(t)_1] / (R^(t) + 1) <= ε'`. This is possible
   because `D^(t)_1` depends on stages `> t` only, which are fixed by then.

Raising `R_0^(1)` afterwards only lowers `ε_1`. Then `Δ_1 <= 2 (w + 1)(2w + 3) ε'`.

## Depths

Let `e = e^(1)` be an independent tower of the same kind, with its own parameters. Left-dominance holds
strictly: `e_v >= 2^(λ + D_v) >= 2^(λ + D_(v+1) + G) > e_(v+1)`. So `max_(v ∈ I_j) e_v = e_(a_j)`, and the
depth coordinates are `f_j + e_(a_j)`. This is Lemma B at the top stage with garbage `E_j = f_j <= c`,
followed by the same recursion (the lower stages only ever see gap sums, exactly as for sizes). So the
depth vectors satisfy `Δ^e_1 <= 2 (w + 1)(2w + 3) ε'` too.

`Y(a, b, f)` is a function of `(n, e)`, and it is the pair of the size vector (a function of `n`) and the
depth vector (a function of `e`). The towers `n` and `e` are independent, so by (T3)

`TV( law Y(a, b, f), law Y(a', b', f') ) <= Δ_1 + Δ^e_1 <= 4 (w + 1)(2w + 3) ε'`.

Choosing `ε' = ε / (4 (w + 1)(2w + 3))` proves the cut-blind property.

## Realizability

This is step 4 of the parameter order in the claim, done after all other choices. Every top parameter
it raises only lowers the error bounds above.
- For each `v`, `e_v >= 2^(R_0^e) >= R_0 + R + max D_1 + 1 >= λ + D_v + 1 >= ⌈log2(n_v + 1)⌉`. The last
  step holds because `n_v + 1 <= 2^(λ + D_v + 1)`.
- Also `e_v < 2^(R_0^e + R^e + max D^e_1 + 1) = 2^(R_0) <= n_v`.

So `⌈log2(n_v + 1)⌉ <= e_v <= n_v`. For every such pair there is a tree with `n_v` carets and depth
`e_v`. For example, `make_tree` in `tower_check.py`:
- it puts a left spine of `e_v` carets;
- it puts balanced right subtrees of total size `n_v − e_v`, each within the depth budget of its spine
  caret;
- the capacity is `2^(e_v) − 1 >= n_v`.

`tower_check.out` verifies it for all `n <= 60` and all admissible `e`. For the general case, proceed
by induction on `e`. With `r = min(n − e, 2^(e−1) − 1)` carets in a balanced right subtree, the left part
needs `n − 1 − r` carets at depth `e − 1`, and `e − 1 <= n − 1 − r <= 2^(e−1) − 1`. ∎

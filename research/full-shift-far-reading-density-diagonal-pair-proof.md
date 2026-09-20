---
rg: 2
id: full-shift-far-reading-density-diagonal-pair-proof
kind: route
title: "Diagonal Følner vectors in l2(X x X): radius-M elements slide them along the diagonal, an element that tells the two points apart knocks them off it, and a weighted sum over pairs gives the cnd function"
target: full-shift-relative-fh-subsets-have-no-far-reading-density
requires: []
---

Notation is as in `full-shift-relative-fh-subsets-have-no-far-reading-density`. For a unitary
representation `π` and a vector `f`, write `ψ_f(g) = ‖π(g)f − f‖²`. This function is cnd, and
`0 ≤ ψ_f ≤ 4‖f‖²`. Finite sums with nonnegative coefficients, and pointwise limits, of cnd
functions are cnd.

## Step 0 (the representation)

- `[[X]]` acts on `X × X` diagonally, `g(y, y') = (gy, gy')`. Let `π` be the permutation
  representation on `ℓ²(X × X)`. The index set is uncountable, which does no harm.
- For `x, x' ∈ X` and an interval `J`, put `p_a = (σ^a x, σ^a x')`, `D = {p_a : a ∈ J}` and
  `f = |J|^{-1/2} 1_D`.
- Put `d = #{a ∈ J : x_{[a−M,a+M]} ≠ x'_{[a−M,a+M]}}` (disagreeing centres), and for `q ∈ [[X]]`
  put `s_q = #{a ∈ J : k_q(σ^a x) ≠ k_q(σ^a x')}`.

## Step 1 (Lemma A: the two estimates)

Assume `x` and `x'` are aperiodic. Then:
- (a) `ψ_f(g) ≤ 2(d + 2‖k_g‖_∞)/|J|` for every `g` with `w(g) ≤ M`;
- (b) `ψ_f(q) ≥ 2 s_q/|J|` for every `q ∈ [[X]]`.

*Proof.*
- `a ↦ p_a` is injective because `x` is aperiodic, so `|D| = |J|` and `‖f‖ = 1`.
- For a bijection `g`, `|gD ∩ D| = |J| − #{p ∈ D : gp ∉ D}`. So
  `ψ_f(g) = 2 − 2|gD ∩ D|/|J| = 2 #{p ∈ D : gp ∉ D}/|J|`.
- (a) Let `a` be an agreeing centre. Then `(σ^a x)_{[−M,M]} = x_{[a−M,a+M]} = (σ^a x')_{[−M,M]}`.
  Since `w(g) ≤ M`, both points have the same value `k = k_g(σ^a x) = k_g(σ^a x')`. So
  `g p_a = p_{a+k}`, and this lies in `D` unless `a + k ∉ J`. With `K = ‖k_g‖_∞`, at most `K`
  such `a` sit at each end of `J`. So `#{p ∈ D : gp ∉ D} ≤ d + 2K`.
- (b) Suppose `k = k_q(σ^a x) ≠ k' = k_q(σ^a x')`. Then `q p_a = (σ^{a+k} x, σ^{a+k'} x')`.
  - If this equals `p_b`, then `σ^{a+k} x = σ^b x` forces `b = a + k`, because `x` is aperiodic.
  - Then `σ^{a+k'} x' = σ^{a+k} x'`, so `k = k'`, because `x'` is aperiodic. This is a
    contradiction.
  - So `q p_a ∉ D`, and `#{p ∈ D : qp ∉ D} ≥ s_q`. ∎

## Step 2 (aperiodicity is free)

- Let `W = max(M, w(q))`. The numbers `d` and `s_q` depend only on `x` and `x'` restricted to the
  finite window `J + [−W, W]`.
- Fix `u ∈ X` that is not eventually periodic in either direction. For example, take the
  concatenation of all binary words in length-lexicographic order on `n ≥ 0`, mirrored on `n < 0`.
- Redefine `x_n = x'_n = u_n` outside `J + [−W, W]`. This changes neither `d` nor `s_q`.
- The new `x` and `x'` agree with `u` off a finite set, so neither is eventually periodic, and in
  particular neither is periodic.
- So the supremum defining `θ_{M,η}` may be taken over aperiodic pairs.

## Step 3 (summation: proof of item 1)

- Let `Θ(Y) = δ_0 > 0` and put `δ = δ_0/2`. `[[X]]` is countable; enumerate it as `g_1, g_2, …`.
- Let `M_j` be the largest window and `K_j` the largest `‖k‖_∞` among `g_1, …, g_j`. Choose
  `η_j > 0` with `(2 + 4K_j) η_j ≤ 4^{-j}/j`.
- Since `sup_{q∈Y} θ_{M_j,η_j}(q) ≥ δ_0 > δ`, there are `q_j ∈ Y` and `(J_j, x_j, x'_j)` with
  `|J_j| ≥ 1/η_j`, `d ≤ η_j|J_j|` (radius `M_j`) and `s_{q_j} > δ|J_j|`. By Step 2 we may take
  `x_j` and `x'_j` aperiodic. Let `f_j` be the Step 0 vector.
- By Lemma A(a), for `i ≤ j`: `ψ_{f_j}(g_i) ≤ 2(η_j|J_j| + 2K_j)/|J_j| ≤ (2 + 4K_j)η_j ≤ 4^{-j}/j`,
  using `1/|J_j| ≤ η_j`. By Lemma A(b), `ψ_{f_j}(q_j) ≥ 2δ`.
- Put `ψ = Σ_j j ψ_{f_j}`. At `g_i` the series is at most `Σ_{j<i} 4j + Σ_{j≥i} 4^{-j} < ∞`. So
  `ψ` is finite everywhere, and cnd as a pointwise limit of cnd partial sums.
- `ψ(q_j) ≥ j ψ_{f_j}(q_j) ≥ 2jδ → ∞`, so `ψ` is unbounded on `Y`. Its restriction to any
  `Γ ⊇ Y` is cnd on `Γ`. ∎

## Step 4 (the Boolean group `H_E`: proof of item 2)

- `σE = {z : z_{−2} = 1, z_{−1} = 0}`. Since `E` needs `y_{−1} = 1` and `σE` needs `y_{−1} = 0`,
  `E ∩ σE = ∅`.
- For clopen `U, V ⊆ E`: `s_U` is an involution with `k = 1_U − 1_{σU}` and `‖k‖ ≤ 1`. If `U` is
  read in `[−w, w]`, then `w(s_U) ≤ w + 1`. On `U ∩ V` the two swaps cancel. `σ(U \ V)`
  lies in `σE`, which misses `V`, and misses `σV`. So `s_U s_V = s_{UΔV}`, and the `s_U` commute.
  Hence `H_E = ⟨q_M⟩` is elementary abelian, infinite since the `U_M` are distinct, inside `B_1`.
  `w(q_M) ≤ M`.
- **The pair.** Fix `M ≥ 1`, `η > 0` and infinite `Λ`. Choose `N` even with `2N + 1 ≥ 1/η`, put
  `J = [−N, N]`, and take `M' ∈ Λ` with `M' ≥ 2N + M + 1`.
  - Let `x_n = 1` iff `n` is odd, for `n ∈ J + [−M, M]`. Choose `x` on `[M' − N, M' + N]`
    arbitrarily, which is disjoint from `J + [−M, M]` because `M' − N > N + M`.
  - Let `x'` equal `x` except on `[M' − N, M' + N]`, where every coordinate is flipped.
  - Extend both by Step 2.
- `x` and `x'` agree on `J + [−M, M]`, so `d = 0`.
- For even `a ∈ J`: `(σ^a x)_{−1} = x_{a−1} = 1` and `(σ^a x)_0 = x_a = 0`, and the same holds for
  `x'`. So both points lie in `E`, hence not in `σE ⊇ σU_{M'}`.
  - `σ^a x ∈ U_{M'}` iff `x_{a+M'} = 0`. Since `a + M' ∈ [M' − N, M' + N]`, exactly one of
    `σ^a x`, `σ^a x'` lies in `U_{M'}`. So the `k` values are `1` and `0`.
- `J` has `N + 1` even points, so `θ_{M,η}(q_{M'}) ≥ (N + 1)/(2N + 1) > 1/2`. Hence
  `Θ({q_M : M ∈ Λ}) ≥ 1/2`, and item 1 applies. ∎
- *Check.* `experiments/diagonal-pair-test-2026-09-17/check_step4.py` builds this pair for several
  `(N, M)` and finds `d = 0` and `s = |J|`. Odd centres separate as well: there both points lie in
  `σE`, and `x_{a+M'−1}` is flipped. So in fact `θ = 1`, but `1/2` is all that is needed.

## Step 5 (the w16 involutions: `Θ({g_m}) = 0`)

- Let `π_m` be the least period of the word `z_{[−m,m]}`. A period of `z_{[−m−1,m+1]}` is a period
  of `z_{[−m,m]}`, so `π_m` is nondecreasing. If it were bounded, one `p` would be a period of
  infinitely many `z_{[−m,m]}`, hence of `z`. So `π_m → ∞`.
- If `y ∈ E_m ∩ σE_m` then `z_n = z_{n+1}` on `[−m, m−1]`, so `π_m = 1`. Thus `g_m` is defined once
  `π_m ≥ 2`, and `w(g_m) ≤ m + 1`.
- Fix `M` and `η`, and a pair `(J, x, x')` as in the definition of `θ_{M,η}`.
  - If `m + 1 ≤ M`: at an agreeing centre both points get the same `k`, so `s ≤ d ≤ η|J|`.
  - If `m ≥ M`: two occurrences of `z_{[−m,m]}` in `x` at distance `0 < p ≤ 2m` make `p` a period
    of that word, so `p ≥ π_m`. Hence `#{a ∈ J : σ^a x ∈ E_m} ≤ |J|/π_m + 1`, and likewise for
    `σE_m` and for `x'`. So `s ≤ 4(|J|/π_m + 1)`.
- Hence `sup_m θ_{M,η}(g_m) ≤ max(η, 4/π_M + 4η)`, which tends to `0` as `M → ∞` and `η → 0`. ∎

## Step 6 (the run-length group: `Θ(H_run) = 0`)

- By Step 4, each `h ∈ H_run` is `s_U` with `U = ⋃_{i∈I} R_i` for a finite `I`. Then
  `y ∈ U` iff `y_{−1} = 1`, `y_{[0,i]} = 0` and `y_{i+1} = 1` for some `i ∈ I`.
- Fix `M ≥ 3` and `η`. Let `a ∈ J` be an agreeing centre with `k_h(σ^a x) ≠ k_h(σ^a x')`. Put
  `y = σ^a x` and `y' = σ^a x'`; they agree on `[−M, M]`.
  - Membership in `E` and in `σE` is read in `[−2, 0]`, so it is the same for `y` and `y'`.
  - If both lie in `E`, membership in `U` differs only if the zero run from `0` is not closed
    inside `[0, M]`, that is, `y_{[0,M]} = 0`. So `a ∈ P = {b : x_{b−1} = 1, x_{[b,b+M]} = 0}`.
  - If both lie in `σE`, membership in `σU` differs only if `y_{−2} = 1` and `y_{[−1,M]} = 0`.
    So `a − 1 ∈ P`.
- Consecutive points of `P` are more than `M + 1` apart, so `#(P ∩ J) ≤ |J|/(M + 1) + 1`.
- So `s ≤ d + 2(|J|/(M + 1) + 1)` and `θ_{M,η}(h) ≤ η + 2/(M + 1) + 2η`, uniformly in `h`. This
  tends to `0`. ∎

## Remark (heuristic, not proved)

- Replacing pairs by `k`-tuples `(σ^a x^{(1)}, …, σ^a x^{(k)})` in `ℓ²(X^k)` gives the same two
  estimates, with `d` the number of centres where some pair disagrees. An element leaves the
  diagonal where some pair is split. The ratio of `q`-sensitivity to generator defect per
  disagreement site is unchanged, so `k`-tuples do not reach `{g_m}` or `H_run`.

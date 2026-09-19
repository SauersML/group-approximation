---
rg: 2
id: thompson-f-product-forest-sets-have-density-below-3-5-proof
kind: route
title: Count the induced Cayley edges of a product window set exactly, tilt the renewal, cap the two edge types by min-overlaps, and split both at the median of the pointer-size law
target: thompson-f-product-forest-sets-have-density-below-3-5
requires:
  - thompson-f-norm-bound-from-forest-renewal-test-vector
  - thompson-f-one-sided-forest-windows-are-norm-lossless
  - thompson-f-norm-bound-from-log-scale-forest-limit
artifacts:
  - experiments/thompson-f-product-set-density-2026-09-17/check_density_formula.py
  - experiments/thompson-f-product-set-density-2026-09-17/check_density_formula_n6.out
---

**Imports.** All are ESTABLISHED nodes of this graph.
- (I1) `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, step 1: `G = <s_0, s_1>` in
  `PL(R)` is isomorphic to `F`, with `s_0, s_1` matching `x_0, x_1` up to the choice of composition
  convention; "inversion `G -> G^op` preserves the symmetric generating set". Step 2: "every move
  `x -> y` by generator `g` satisfies `E(y) = g E(x)` in `G`: it is a Cayley edge", and
  "*Injectivity.* `E` determines the state."
- (I2) `thompson-f-one-sided-forest-windows-are-norm-lossless`, item 1: "The induced subgraph of the
  Cayley graph on `E(S_n)` is exactly the move graph on `S_n`".
- (I3) `thompson-f-norm-bound-from-log-scale-forest-limit-proof`, step 2, as used in
  `thompson-f-product-forest-vectors-stay-below-71-72-proof`, step 1:
  "`p'` has finite support and `p'_1 > 0`. So step 2 of
  `thompson-f-norm-bound-from-log-scale-forest-limit-proof` (whose argument uses only these two
  facts) gives `Y'_{n-j} / Y'_n -> 1`." Here `Y' = Z' * Z'`, and `Z'` is the renewal sequence of the
  probability vector `p'`.

*Density convention.* Guba's density of a finite `Y` is its average vertex degree in the induced
Cayley subgraph. The left and right Cayley graphs are exchanged by `y -> y^{-1}`, and so are the two
composition conventions in (I1). Both maps are bijections that preserve induced degrees. So `δ(Y)`
may be computed in the graph `x ~ x o g`, `g ∈ {s_0^±1, s_1^±1}`, of (I2).

Fix a product forest family `(N, 𝒜, ℬ)` as in the claim, and the counts `a_s, b_s, x_s, e_m`, `W`,
`Y` defined there.

1. **Exact counting at fixed `n`.**
   - *Vertices.* By (I1), `|Y_n|` is the number of states `(λ, P, ρ)`, where:
     - `λ = (T_0..T_{i-1})` is a sequence of `𝒜`-trees;
     - `P = T_i ∈ ℬ`;
     - `ρ` is a sequence of `𝒜`-trees;
     - the leaf total is `n`.

     The number of pairs `(λ, ρ)` with `k` leaves in total is `sum_{l} W_l W_{k-l} = Y_k`. So
     `|Y_n| = sum_s b_s Y_{n-s} = D_n`.
   - *Edges.* By (I2), the induced edges of `Y_n` are the moves with both ends in the set. Each
     state has at most one move per generator, so `<1_Y, K 1_Y>` is the number of directed moves
     inside the set. Pointer-left reverses pointer-right, and split reverses merge. So this number is
     `2 (#pointer-right + #merge)`, counted over moves with both ends in the set.
     - *Pointer right* sends `(λ, P, U, ρ'; i)` to the same forest with pointer `i + 1`. The source
       needs `P ∈ ℬ` and `U ∈ 𝒜`; the target needs `P ∈ 𝒜` and `U ∈ ℬ`. So `P, U ∈ 𝒜 ∩ ℬ`, and
       the other trees lie in `𝒜`. These configurations number `Sh_n = sum_{s,t} x_s x_t Y_{n-s-t}`.
     - *Merge* replaces `P, U` by `(P, U)`. The source needs `P ∈ ℬ` and `U ∈ 𝒜`; the target needs
       `(P, U) ∈ ℬ`. So the merged tree `T = (P, U)` is one of the `e_m` trees counted in `e_m`, and
       these configurations number `Mg_n = sum_m e_m Y_{n-m}`.
   - Hence `δ(Y_n) = 2 (Sh_n + Mg_n) / D_n`. This is item 1 of the claim.
   - `check_density_formula.py` part A confirms it by brute force. It uses exact PL arithmetic, tests
     every one of the four Cayley neighbours of every element for membership, and covers
     240 (family, `n`) pairs with `n <= 6`, including families with the leaf outside `𝒜`.

2. **Tilt and limit.**
   - `E(x) = sum_{s<=N} a_s x^s` is a polynomial with `E(0) = 0`, nonnegative coefficients, and
     `a_1 = 1` (the leaf is in `𝒜`). So `E` increases on `[0, inf)`, and `E(1) >= 1`. Hence there
     is a unique `R ∈ (0, 1]` with `E(R) = 1`.
   - Put `η_s = a_s R^s`. This is a probability vector on `{1..N}`, with `η_1 = R > 0`.
   - `W'_l = W_l R^l` is the renewal sequence of `η`, and `Y'_k = Y_k R^k = (W' * W')(k)`.
   - By (I3), applied with `p' = η`, we get `Y_{n-j} / Y_n = R^j Y'_{n-j} / Y'_n -> R^j` for each
     fixed `j`. Also `Y_n >= W_0 W_n >= 1`, since `W_n` counts at least the all-leaves sequence.
   - `D_n / Y_n`, `Sh_n / Y_n` and `Mg_n / Y_n` are finite sums, over `s, t, m <= N`, of fixed
     coefficients times `Y_{n-j} / Y_n`. So they converge to
     - `Q = sum_s b_s R^s > 0`,
     - `(sum_s x_s R^s)^2`,
     - `sum_m e_m R^m`.
   - Hence `δ_∞ = lim δ(Y_n) = 2 [ (sum_s x_s R^s)^2 + sum_m e_m R^m ] / Q`, which is item 2.

3. **Relaxation to `Ψ`.** Put `ν_s = b_s R^s / Q`, a probability vector on `{1..N}`.
   - *Shift.* `x_s <= min(a_s, b_s)`, since `𝒜_s ∩ ℬ_s` lies in both sets. So
     `sum_s x_s R^s <= sum_s min(η_s, Q ν_s) = sqrt(Q) S(u_0)`, where `u_0 = Q^{-1/2}` and
     `S(u) = sum_s min(u η_s, ν_s / u)`. So `(sum_s x_s R^s)^2 / Q <= S(u_0)^2 <= max_u S(u)^2`.
   - *Merge.* Two bounds hold for `e_m`.
     - `e_m <= b_m`, since the trees counted lie in `ℬ_m`.
     - `e_m <= (b * a)(m) = sum_{k+l=m} b_k a_l`, since `T -> (L, R)` injects them into pairs with
       `L ∈ ℬ_k` and `R ∈ 𝒜_l`.

     Also `(b * a)(m) R^m = sum_{k+l=m} (b_k R^k)(a_l R^l) = Q (ν * η)(m)`. So
     `sum_m e_m R^m / Q <= sum_m min(ν_m, (ν * η)(m))`.
   - Hence `δ_∞ <= 2 Ψ(ν, η)` with `Ψ = max_u S(u)^2 + sum_m min(ν_m, (ν * η)(m))`. Here `m` runs
     over `{1..N}`, and terms beyond `N` would only add.

4. **Cap: `Ψ(ν, η) <= 3/2 + α^2 < 7/4` for all probability vectors `ν, η` on the positive
   integers with finite support.**
   Let `X ~ ν` and `Y ~ η` be independent, with cdfs `F` and `G`. Let `t >= 1` be the least integer
   with `F(t) >= 1/2`, and put `α = F(t-1) < 1/2` and `β = G(t-1)`. (`F(0) = G(0) = 0`.)
   - *Merge term.* Split the sum at `t`:
     `sum_m min(ν_m, (ν*η)(m)) <= sum_{m<=t} (ν*η)(m) + sum_{m>t} ν_m = P(X + Y <= t) + 1 - F(t)`.
     Since `X, Y >= 1`, the event `X + Y <= t` forces `X <= t-1` and `Y <= t-1`. So the merge term
     is at most `α β + 1/2`.
   - *Shift term.* Let `I = {1..t-1}` and `J = {t, t+1, ...}`. For `p, q, u > 0`,
     `min(u p, q/u)` is superadditive in the pair `(p, q)`: for sums, `sum_s min(u p_s, q_s/u) <=
     min(u sum p_s, sum q_s / u)`. So
     `S(u) <= h(u) := min(u β, α / u) + min(u (1 - β), (1 - α) / u)`.
     - *Case `β <= α`.* By AM-GM and Cauchy–Schwarz, `S(u) <= sum_s sqrt(η_s ν_s) <= 1`.
     - *Case `β > α`.* Then `α/β < 1 < (1-α)/(1-β)`, reading the right side as `+inf` when `β = 1`.
       Put `u_1 = sqrt(α/β)` and `u_2 = sqrt((1-α)/(1-β))`.
       - For `u <= u_1`, both minima take their first entry, so `h(u) <= u β + u (1-β) = u <= u_1`.
       - For `u >= u_2`, both take their second, so `h(u) <= α/u + (1-α)/u = 1/u <= 1/u_2`.
       - For `u_1 < u < u_2`, `h(u) <= α/u + u(1-β)`. This is convex in `u`, so it is at most the
         larger of its two endpoint values: `sqrt(αβ) + sqrt(α/β)(1-β) = u_1` at `u_1`, and
         `α/u_2 + sqrt((1-α)(1-β)) = (α + 1 - α)/u_2 = 1/u_2` at `u_2`. (If `β = 1`, then
         `h(u) <= α/u < sqrt(α)` on this range.)

       So `max_u S(u)^2 <= max(α/β, (1-β)/(1-α))`.
   - *Combine.*
     - If `β <= α`: `Ψ <= 1 + 1/2 + αβ <= 3/2 + α^2`.
     - If `β > α`, the first branch is `φ_1(β) = α/β + αβ + 1/2` on `(α, 1]`.
       - For `α > 0`, `φ_1` is convex, so it is at most `max(1 + α^2, 2α) + 1/2 = 3/2 + α^2`.
       - For `α = 0`, `φ_1 = 1/2`.
     - The second branch `φ_2(β) = (1-β)/(1-α) + αβ + 1/2` is affine in `β`. So it is at most
       `max(1 + α^2, α) + 1/2 = 3/2 + α^2`.
   - Since `α < 1/2`, `Ψ <= 3/2 + α^2 < 7/4`. With step 3 this gives
     `δ_∞ <= 2Ψ <= 3 + 2α^2 < 3.5`, which is item 3.
   - Float sanity check (not used): `check_density_formula.py` part C evaluates `Ψ` exactly in `u`,
     at the breakpoints `u^2 = ν_s / η_s`, on 3000 random pairs. All obey `Ψ <= 3/2 + α^2`.

5. **Sharpness: the depth-`<= k` family.** Take `𝒜 = ℬ = 𝒟_k` (`k >= 1`). The leaf is in `𝒟_k`,
   and `N = 2^k`.
   - `x_s = a_s = b_s`. If `T = (L, R) ∈ 𝒟_k`, then `L, R ∈ 𝒟_{k-1} ⊂ 𝒟_k`, so `e_m = b_m` for
     `m >= 2`, and `e_1 = 0`.
   - The generating function of `𝒟_k` by leaves is `D_k(x)`, with `D_0 = x` and
     `D_k = x + D_{k-1}^2`. So `R = R_k` solves `D_k(R_k) = 1`, and `Q = sum b_s R^s = 1`.
   - Step 2 gives `δ_∞ = 2 [1 + (1 - R_k)] / 1 = 4 - 2 R_k`.
   - *`R_k > 1/4`.* For `0 <= x <= 1/4`, induction gives `D_j(x) <= 1/4 + (1/2)^2 = 1/2 < 1`.
   - *`R_k` strictly decreasing.* For `x > 0`, `D_1 - D_0 = x^2 > 0` and
     `D_k - D_{k-1} = D_{k-1}^2 - D_{k-2}^2 > 0` by induction. So `D_k(R_{k-1}) > 1`, and hence
     `R_k < R_{k-1}`.
   - *`R_k -> 1/4`.* Fix `x > 1/4`. The sequence `D_j(x)` increases in `j`. If it were bounded, its
     limit `L` would satisfy `L = x + L^2`, which has no real root when `x > 1/4`. So `D_k(x) > 1`
     for some `k`, and then `R_k < x`.
   - Hence `4 - 2R_k` increases strictly to `3.5`, which is item 4.
   - `check_density_formula.py` part B gives the numbers:
     - it bisects `R_k` in exact rationals for `k <= 14`;
     - it checks the monotonicity and `R_k > 1/4`;
     - for `k <= 5` it recomputes `δ_∞` from the general step-2 formula, using exact size counts
       of `𝒟_k`;
     - part A includes depth families among its brute-force checks.

6. **Conclusion.** Every product forest family has `δ_∞ < 3.5` (step 4), and the depth families
   approach `3.5` (step 5). So `sup δ_∞ = 3.5`, and it is never attained. □

*Where the argument would break at finite `n` (recorded for the Attempts).* Step 2 is the only
place where `n -> infinity` is used. It makes the weight `Y_{n-s-t}` factor as `R^s R^t`, and this
makes the pointer size and the neighbour size independent. That independence drives both the bound
`P(X + Y <= t) <= αβ` and the product form of the shift term. At finite `n` the joint law of
(pointer size, neighbour size) is proportional to `b_s a_t Y_{n-s-t}`. It is positively associated
whenever `k -> Y_{n-k}` is log-convex, and the two median estimates then decouple. The same split
still gives `Sh_n + Mg_n <= (3/2 + α) D_n`, which is too weak.

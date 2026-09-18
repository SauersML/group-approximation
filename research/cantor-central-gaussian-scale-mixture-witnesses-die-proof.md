---
rg: 2
id: cantor-central-gaussian-scale-mixture-witnesses-die-proof
kind: route
title: "Lift the wrapped pair laws near 0, pass to scale-free angular laws, force every normalized pair Gram to one symmetric limit, and contradict quadratic inclusion-exclusion at the pair (U1⊔U2⊔U3, U4)"
target: cantor-central-gaussian-scale-mixture-witnesses-die
requires: []
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Notation is as in the target. `⊔` is disjoint union. A *proper pair* is an ordered pair
`P = (W, W')` of disjoint nonempty clopens with `W ⊔ W' ≠ C`. For a law `ν ∈ 𝒢` with data
`(m, Y, s, Q)` put `X = m + √s·Y`, `X_P = (X(1_W), X(1_{W'})) ∈ R²`, `μ_P = law(X_P)`, and
`Γ_P` for the `2×2` Gram matrix of `Q` on `(1_W, 1_{W'})`. Push-forwards and marginals do not
increase `d`.

## 0. Transitivity

**Fact 0.** `V` acts transitively on proper pairs.

This is the case `k = 2` of the artifact §3(e) ("`V` acts transitively on ordered `k`-tuples of
pairwise disjoint nonempty clopen sets whose union has nonempty complement"). Direct proof:
- Each of `W`, `W'` and `C ∖ (W ⊔ W')` is a nonempty finite disjoint union of cones.
- Splitting a cone `[u] = [u0] ⊔ [u1]` raises the count by one. So for two proper pairs the three
  pieces can be written with equal numbers of cones.
- The prefix replacement matching those cones in order is an element of `V`.

Fix `U_1 = [000]`, `U_2 = [001]`, `U_3 = [010]`, `U_4 = [011]`, with `U_1 ⊔ … ⊔ U_4 = [0]`, and the
reference pair `P_0 = (U_1, U_2)`. For every proper pair `P = (W, W')` fix `g_P ∈ V` with
`g_P W = U_1` and `g_P W' = U_2`. Since `(g·χ)(1_U) = χ(1_{g^{-1}U})`, the
`(1_{U_1}, 1_{U_2})`-marginal of `g_{P*}ν` is the `(1_W, 1_{W'})`-marginal of `ν`.

## 1. Lifting near 0

**Lemma 1.** Let `ζ ~ N(0, v)` with `v ≥ 0` and `0 < ε ≤ 1/6`. Then
`P(|ζ| ≥ 1/2) ≤ P(dist(ζ, ℤ) > ε) + 3ε`. The same holds for every mixture of centred normals.

*Proof.* The case `v = 0` is trivial. Let `v > 0`.
- If `|ζ| ≥ 1/2` and `dist(ζ, ℤ) ≤ ε`, then `ζ ∈ I_n = [n − ε, n + ε]` for some `n ≠ 0`.
- For `n ≥ 1` let `J_n = [n − 1 + ε, n − ε]`. These are disjoint subsets of `[ε, ∞)`.
- The density `φ` of `ζ` decreases on `[0, ∞)`. So `P(I_n) ≤ 2ε φ(n − ε)` and
  `P(J_n) ≥ (1 − 2ε) φ(n − ε)`.
- Hence `Σ_{n≥1} P(I_n) ≤ (2ε/(1−2ε)) P(ζ ≥ ε) ≤ 3ε · (1/2)`, using `ε ≤ 1/6`.
- By symmetry the same bound holds for `n ≤ −1`.

A mixture is handled by averaging the bound over the mixing variable. ∎

**Corollary 1.** Let `ν_k ∈ 𝒢` be centred (`m_k = 0`) with `ν_k → δ_0`. Then for each clopen `W`,
`τ_k(W) := P(|X_k(1_W)| ≥ 1/2) → 0`.

*Proof.*
- Conditionally on `s_k`, `X_k(1_W)` is centred normal, so Lemma 1 applies.
- The set `F_ε = {χ : ‖χ(1_W)‖_T ≥ ε}` is closed in `Â` and misses `0`. So weak convergence gives
  `limsup_k P(dist(X_k(1_W), ℤ) ≥ ε) = limsup_k ν_k(F_ε) ≤ δ_0(F_ε) = 0`.
- Hence `limsup_k τ_k(W) ≤ 3ε` for every `ε ∈ (0, 1/6]`. ∎

**Lemma 2 (pair transfer).** For a centred `ν ∈ 𝒢` and a proper pair `P = (W, W')`,
`d(μ_P, μ_{P_0}) ≤ d(g_{P*}ν, ν) + τ(W) + τ(W') + τ(U_1) + τ(U_2)`.

*Proof.*
- Let `w_P = law(X_P mod ℤ²)`, the `(1_W, 1_{W'})`-marginal of `ν`. By §0,
  `d(w_P, w_{P_0}) ≤ d(g_{P*}ν, ν)`.
- Let `L : T² → (−1/2, 1/2]²` be the Borel inverse of reduction mod `ℤ²`. On the event
  `X_P ∈ (−1/2, 1/2)²` we have `L(X_P mod ℤ²) = X_P`.
- So `d(L_*w_P, μ_P) ≤ P(X_P ∉ (−1/2,1/2)²) ≤ τ(W) + τ(W')`. The same holds for `P_0`.
- Apply the triangle inequality, using `d(L_*w_P, L_*w_{P_0}) ≤ d(w_P, w_{P_0})`. ∎

## 2. Angular laws

Let `Φ : R² → S¹ ⊔ {†}` be `Φ(x) = x/|x|` for `x ≠ 0` and `Φ(0) = †`, and let
`K = {Γ ∈ R^{2×2} : Γ ⪰ 0, tr Γ = 1}`, a compact set. For `Γ ⪰ 0` with `Γ ≠ 0`, let
`ACG(Γ) = law Φ(Γ^{1/2} ξ)`, with `ξ` standard normal in `R²`. It is a law on `S¹`, since
`Γ^{1/2}ξ ≠ 0` a.s., and `ACG(tΓ) = ACG(Γ)` for `t > 0`.

**Lemma 3.**
- (a) Let `ν ∈ 𝒢` be centred and `P` a proper pair. If `Γ_P = 0` then `Φ_*μ_P = δ_†`. If
  `Γ_P ≠ 0` then `Φ_*μ_P = ACG(Γ_P)`, whatever the law of `s`.
- (b) `Γ ↦ ACG(Γ)` is injective and weakly continuous on `K`.
- (c) For every `η > 0` there is `θ > 0` such that `Γ, Γ' ∈ K` and `d(ACG(Γ), ACG(Γ')) ≤ θ`
  imply `‖Γ − Γ'‖ ≤ η`.

*Proof.*
- (a) `Y_P := (Y(1_W), Y(1_{W'}))` has the law of `Γ_P^{1/2}ξ`. Conditionally on `s > 0`,
  `Φ(√s Y_P) = Φ(Y_P)`. So `Φ(X_P) = Φ(Y_P)` a.s., and the law of `s` drops out.
- (b), rank 2. `Γ^{1/2}ξ` has density `(2π)^{-1}(det Γ)^{-1/2} exp(−xᵀΓ^{-1}x/2)`. In polar
  coordinates, `∫_0^∞ e^{−r²q/2} r dr = 1/q`. So `ACG(Γ)` has density
  `(2π)^{-1}(det Γ)^{-1/2}(uᵀΓ^{-1}u)^{-1}` with respect to arc length. It is continuous and
  strictly positive, and it determines the quadratic form `u ↦ uᵀΓ^{-1}u` up to a positive factor.
  Hence it determines `Γ` up to scale, and `Γ` itself on `K`.
- (b), rank 1. For `Γ = vvᵀ`, `Γ^{1/2}ξ = v(vᵀξ)/|v|`, so `ACG(Γ) = ½(δ_{v/|v|} + δ_{−v/|v|})`.
  This determines `v` up to sign, hence `Γ`.
- (b), mixed ranks. A rank-1 law is atomic and a rank-2 law is absolutely continuous, so they
  differ. This proves injectivity.
- (b), continuity. If `Γ_k → Γ` in `K` then `Γ_k^{1/2}ξ → Γ^{1/2}ξ` a.s. (the matrix square root
  is continuous), and `Φ` is continuous off the null event `{Γ^{1/2}ξ = 0}`.
- (c) Suppose not. Then there are `Γ_k, Γ'_k ∈ K` with `d(ACG(Γ_k), ACG(Γ'_k)) → 0` and
  `‖Γ_k − Γ'_k‖ > η`.
  - Pass to a subsequence with `Γ_k → Γ` and `Γ'_k → Γ'`, so `‖Γ − Γ'‖ ≥ η`.
  - For bounded continuous `f`, `|∫f dACG(Γ_k) − ∫f dACG(Γ'_k)| ≤ 2‖f‖_∞ d(·,·) → 0`.
  - By (b) the two sides converge to `∫f dACG(Γ)` and `∫f dACG(Γ')`. So `ACG(Γ) = ACG(Γ')`, and
    `Γ = Γ'` by injectivity, a contradiction. ∎

## 3. The centred case

**Theorem 4.** Let `ν_k ∈ 𝒢` be centred, with covariance forms `Q_k`, satisfying conditions 1 and
2 of the target. Then for every nonempty clopen `W ≠ C`, `Q_k(1_W) = 0` for all large `k`. Hence
`Q_k(1_C) ≤ 2(Q_k(1_{[0]}) + Q_k(1_{[1]})) = 0` for all large `k`, so `X_k(1_C) = 0` a.s. and
`ν_k{χ(1_C) = 1} = 1`.

*Proof.* Fix `W`. Choose a nonempty clopen `W̃ ⊊ C ∖ W`, so that `(W, W̃)` is a proper pair. Let
`𝒫` consist of the proper pairs
- `(U_i, U_j)` for `1 ≤ i < j ≤ 4`, and `(U_2, U_1)`;
- `(U_1 ⊔ U_2, U_3)` and `(U_1 ⊔ U_2 ⊔ U_3, U_4)` (the unions are proper because
  `U_1 ⊔ … ⊔ U_4 = [0]`);
- `(W, W̃)`.

Let `δ_k = max_{P∈𝒫} d(g_{P*}ν_k, ν_k) + 4 max_U τ_k(U)`, where `U` runs over the finitely many
sets occurring in `𝒫`. By condition 1 and Corollary 1, `δ_k → 0`. By Lemma 2,
`d(μ^k_P, μ^k_{P_0}) ≤ δ_k` for all `P ∈ 𝒫`.

*Step 1 (degeneracy is all or nothing).* Let `δ_k < 1`. By Lemma 3(a), `Φ_*μ^k_P` is `δ_†` when
`Γ^k_P = 0` and is carried by `S¹` otherwise. Two such laws of different kinds are at distance
`1`, and `d(Φ_*μ^k_P, Φ_*μ^k_{P_0}) ≤ δ_k < 1`. So `Γ^k_P = 0` iff `Γ^k_{P_0} = 0`.

*Step 2 (one symmetric limit).* Suppose the claim fails for `W`. Then for infinitely many `k`,
`Q_k(1_W) > 0`, so `Γ^k_{(W,W̃)} ≠ 0`, and by Step 1 `Γ^k_P ≠ 0` for every `P ∈ 𝒫`. Pass to
these `k`.
- Put `Γ̂^k_P = Γ^k_P / tr Γ^k_P ∈ K`. By Lemma 3(a), `Φ_*μ^k_P = ACG(Γ̂^k_P)`.
- So `d(ACG(Γ̂^k_P), ACG(Γ̂^k_{P_0})) ≤ δ_k → 0`, and by Lemma 3(c),
  `‖Γ̂^k_P − Γ̂^k_{P_0}‖ → 0`.
- Pass to a further subsequence with `Γ̂^k_{P_0} → M ∈ K`. Then `Γ̂^k_P → M` for every `P ∈ 𝒫`.
- With `J` the coordinate swap, `Γ̂_{(U_2,U_1)} = J Γ̂_{(U_1,U_2)} J`. So `M = JMJ`, i.e.
  `M = [[1/2, β], [β, 1/2]]` for some `β`.

*Step 3 (ratios).* For `P = (W_1, W_2) ∈ 𝒫` write `a = Q_k(1_{W_1})`, `b = Q_k(1_{W_2})` and
`c = Q_k(1_{W_1}, 1_{W_2})`. Step 2 gives `a/(a+b) → 1/2` and `c/(a+b) → β`. So for large `k`,
`a, b > 0`, `a/b → 1` and `c/a → 2β`. Write `q_i = Q_k(1_{U_i})` and `c_ij = Q_k(1_{U_i}, 1_{U_j})`.
- The pairs `(U_i, U_j)`, `i < j`, give `q_i/q_j → 1` and `c_ij/q_i → 2β`. Hence
  `c_ij/q_l → 2β` for all `l ≤ 4`.
- `Q_k` is bilinear, since `Y_k` is a.s. additive. So `Q_k(1_{U_1⊔U_2}) = q_1 + q_2 + 2c_12`. The
  pair `(U_1 ⊔ U_2, U_3)` gives `Q_k(1_{U_1⊔U_2})/q_3 → 1`. The left side tends to `2 + 4β`, so
  `β = −1/4`.
- Also `Q_k(1_{U_1⊔U_2⊔U_3}) = q_1 + q_2 + q_3 + 2(c_12 + c_13 + c_23)`. The pair
  `(U_1 ⊔ U_2 ⊔ U_3, U_4)` gives `Q_k(1_{U_1⊔U_2⊔U_3})/q_4 → 1`. But the left side tends to
  `3 + 6·2β = 3 − 3 = 0`.

This contradiction proves the claim for `W`.

For the last sentence: `1_C = 1_{[0]} + 1_{[1]}` and `Q(f+f') ≤ 2Q(f) + 2Q(f')`. So `Y_k(1_C)`
is centred Gaussian with variance `0`, and `X_k(1_C) = √s_k·Y_k(1_C) = 0` a.s. ∎

*Remark (the invariant).* Step 3 is the scale-free version of the artifact §3(e). A `V`-invariant
positive semidefinite form takes one value `q` on indicators of proper clopens and `−q/2` on
proper pairs. Then inclusion–exclusion gives `q = Q(1_{U_1⊔U_2⊔U_3}) = 3q + 6·(−q/2) = 0`. Here almost invariance holds only up to an
unknown scale per pair, and it is the angular laws that make it usable. Wrapping mod `1` is
harmless because the witnesses concentrate at `0` (Lemma 1).

## 4. Deterministic means, and the theorem

**Theorem 5.** Let `ν_k ∈ 𝒢`, with data `(m_k, Y_k, s_k, Q_k)`, satisfy conditions 1 and 2. Then
`ν_k{χ(1_C) = 1} = 1` for all large `k`. In particular condition 3 fails, which proves the target.

*Proof.* Write `ν̌` for the law of `−χ`, and put `ν'_k = ν_k * ν̌_k`, the law of `χ − χ'` for
independent `χ, χ' ~ ν_k`.
- *`ν'_k` is centred in `𝒢`, with the same `Q_k`.* Realize `χ = e∘(m_k + √s Y)` and
  `χ' = e∘(m_k + √s' Y')` with independent copies. Then `χ − χ' = e∘(√s Y − √s' Y')`.
  Conditionally on `(s, s')`, `√s Y − √s' Y'` is a centred Gaussian random homomorphism with
  covariance `(s + s')Q_k`, i.e. it has the law of `√(s+s')·Y`. And `s + s' > 0` a.s.
- *Condition 1.* `g` acts on `Â` by a continuous automorphism, so
  `g_*(ν * ν̌) = (g_*ν) * (g_*ν)ˇ`. For laws `μ_1, μ_2`,
  `d(μ_1 * μ̌_1, μ_2 * μ̌_2) ≤ d(μ_1 * μ̌_1, μ_2 * μ̌_1) + d(μ_2 * μ̌_1, μ_2 * μ̌_2) ≤ 2 d(μ_1, μ_2)`.
  So `d(g_*ν'_k, ν'_k) ≤ 2 d(g_*ν_k, ν_k) → 0`.
- *Condition 2.* The Fourier coefficient of `ν'_k` at `f ∈ A` is `|∫ e(χ(f)) dν_k|² → 1`.
  Trigonometric polynomials are dense in `C(Â)` (Stone–Weierstrass), so `ν'_k → δ_0`.

By Theorem 4 applied to `ν'_k`: for each finite family `F` of nonempty clopens `W ≠ C`,
`Q_k(1_W) = 0` for all `W ∈ F` and all large `k`, and also `Q_k(1_C) = 0`.
- Take `F = {[0], [1], [00], [01]}`. For large `k`, `X_k(1_W) = m_k(1_W)` a.s. for
  `W ∈ F ∪ {C}`. So the `(1_W)_{W∈F}`-marginal of `ν_k` is the point mass at `(t_W)_W` with
  `t_W = m_k(1_W) mod 1`.
- Fix `h_1, h_2, h_3 ∈ V` with `h_1[00] = [0]`, `h_2[01] = [0]`, `h_3[1] = [0]` (Fact 0 with a
  cone in place of a pair, or explicit prefix replacements). The `1_{[0]}`-marginal of `h_{i*}ν_k`
  is the point mass at `t_{h_i^{-1}[0]}`, and that of `ν_k` is the point mass at `t_{[0]}`.
- Two different point masses are at distance `1`. So condition 1 gives, for large `k`,
  `t_{[00]} = t_{[01]} = t_{[1]} = t_{[0]}`.
- Additivity of `m_k` gives `t_{[0]} = t_{[00]} + t_{[01]} = 2t_{[0]}` in `T`, so `t_{[0]} = 0`.
  Then `t_{[1]} = 0` and `m_k(1_C) ≡ t_{[0]} + t_{[1]} = 0 mod 1`.
- Since `Q_k(1_C) = 0`, `X_k(1_C) = m_k(1_C) ∈ ℤ` a.s. Hence `χ(1_C) = 1` `ν_k`-a.s. ∎

## 5. What this does and does not cover

- **Covered.** Every law `e∘(m + √s Y)`: any covariance whatever (white noise, halving trees,
  log-correlated or free-field charges, long-range or scale-free structure), any deterministic
  mean, and any independent random scale, including a scale whose law `V` shifts. For each fixed
  `W` the proof uses only the finitely many elements `g_P` (`P ∈ 𝒫`) and `h_1, h_2, h_3`.
- **Not covered.**
  - Mixtures over a random covariance shape: the angular law of a pair is then a mixture of
    `ACG` laws, and Lemma 3(c) has no mixture analogue. Mixtures of centred normals over random
    covariances in `R²` are not identifiable. For example, `vvᵀ` with `v` uniform on `S¹`, and
    `σI` with `σ` chosen so that `σ·χ²_2 = χ²_1` in law, give the same law. Such a `σ` exists
    because the `χ²_1` density is completely monotone, hence a mixture of exponentials.
  - Random means.
  - Non-Gaussian infinitely divisible laws. The canonical witnesses from a cnd `ψ` are
    `e^{−tψ}`-laws. These are compound Poisson on `A`, because the Gaussian part
    `Q_ψ(f) = lim_N ψ(Nf)/N²` of `ψ|_A` vanishes, as follows.
    - By Lévy–Khinchin, `ψ|_A = Q_ψ + ∫(1 − cos 2πχ(·)) dL`. The jump term is `o(N²)` along `Nf`,
      by dominated convergence and `|sin(Nθ/2)| ≤ N|sin(θ/2)|`.
    - Since `√ψ(h·f) ≤ √ψ(f) + 2√ψ(h)`, dividing by `N` gives `Q_ψ(h·f) ≤ Q_ψ(f)` for every
      `h ∈ V`, and so `Q_ψ` is `V`-invariant.
    - Then `Q_ψ = 0` by the artifact §3(e).

  A witness, if one exists, is therefore of jump type or has a genuinely random covariance shape.

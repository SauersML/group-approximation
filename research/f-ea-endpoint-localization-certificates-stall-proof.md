---
rg: 2
id: f-ea-endpoint-localization-certificates-stall-proof
kind: route
title: Bound the confined rate by a reflected lazy walk killed at depth W, bound comparison words below by the doubling bound on generators, and multiply
target: f-ea-endpoint-localization-certificates-stall
requires: [f-dyadic-endpoint-switch-walk-gaps-are-inverse-square, thompson-f-point-orbits-are-transient]
---

Notation as in the claim and in `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof`.

## Step 1. Linear action in the zones

**(1a) Zone `Z_0`.** On `[0,1/4]`, `x_0` halves, `x_0^{−1}` doubles, and `x_1^{±1}`, `e` fix. Put `σ(x_0) = +1`,
`σ(x_0^{−1}) = −1`, `σ = 0` otherwise, and `S_k = Σ_{l≤k} σ(h_l)`, `S_0 = 0`.
- Fix `k` and put `z_{k+1} = y`, `z_j = h_j^{−1} z_{j+1}`. On `E_n` every `z_{j+1}` lies in `Z_0`, so by downward
  induction `z_j = 2^{S_k − S_{j−1}} y`.
- The condition `z_j ≤ 1/4` is `S_k − S_{j−1} ≤ log_2(1/(4y))`, that is `S_k − S_{j−1} ≤ W`.
- So `E_n ⊆ G_n := {M_k ≤ W for all k ≤ n}`, where `M_k = S_k − min_{0≤i≤k} S_i`.

**(1b) Zone `Z_1`.** Write `u(t) = 1 − t`. On `[3/4,1]`, `x_0(t) = 2t − 1`, and on `[7/8,1]`, `x_1(t) = 2t − 1`.
So for `u(z) ≤ 1/8`, both `x_0` and `x_1` double `u`, and both `x_0^{−1}` and `x_1^{−1}` halve `u` (on `[3/4,1]`
they are `t ↦ (t+1)/2`). Since `z_j = h_j^{−1} z_{j+1}`, put `σ(x_0^{−1}) = σ(x_1^{−1}) = +1`,
`σ(x_0) = σ(x_1) = −1`, `σ(e) = 0`.
- As in (1a), `u(z_j) = 2^{S_k − S_{j−1}} u(y)` on `E_n`, and `u(z_j) ≤ 1/8` gives `E_n ⊆ G_n` with
  `W = ⌊log_2(1/(8u(y)))⌋`.

## Step 2. The rate bound

**(2a) Reflected walk.** `M` is a Markov chain on `{0,1,…}` (a step down from `0` creates a new minimum and leaves
`M = 0`). Killed above `W`, its kernel `K'` on `{0,…,W}` is:
- in `Z_0`: `K'(i,i±1) = 1/5`, `K'(i,i) = 3/5` for `i ≥ 1`, and `K'(0,0) = 4/5`, `K'(0,1) = 1/5`;
- in `Z_1`: `K'(i,i±1) = 2/5`, `K'(i,i) = 1/5` for `i ≥ 1`, and `K'(0,0) = 3/5`, `K'(0,1) = 2/5`.

**(2b) Eigenvector.** `K'` is symmetric. Put `φ(i) = cos(π(i+½)/(2W+3))` for `0 ≤ i ≤ W`.
- It is positive on `{0,…,W}`, and its extension satisfies `φ(−1) = φ(0)` and `φ(W+1) = cos(π/2) = 0`.
- So the reflecting boundary at `0` and the killing at `W+1` are both satisfied, and `φ` is an eigenvector with
  eigenvalue `θ' = 3/5 + (2/5)cos(π/(2W+3))` in `Z_0` and `θ' = 1/5 + (4/5)cos(π/(2W+3))` in `Z_1`.
- By Perron–Frobenius, `θ'` is the top eigenvalue, and `‖K'^n‖ = θ'^n` since `K'` is symmetric and nonnegative.

**(2c) Rate.** `E[2^{−|O_n^y|}; E_n] ≤ P(G_n) = ⟨δ_0, K'^n 1⟩ ≤ √(W+1)·θ'^n`. So `r ≤ θ'`.
- Using `1 − cos x ≥ 2x²/π²` for `|x| ≤ π`: `1 − r ≥ 4/(5(2W+3)²)` in `Z_0` and `1 − r ≥ 8/(5(2W+3)²)` in `Z_1`. ∎

## Step 3. Comparison words are long

**(3a) Where lamps move.** Let `π : L → F` be the projection. An atom `t = δ_y^a s δ_y^b` equals
`({y}^a Δ s{y}^b, s)`. For a word `t_1⋯t_ℓ` put `p_i = π(t_1⋯t_i)`. From `(φ,g)(φ',g') = (φ Δ gφ', gg')`, the lamp
configuration of the product is a symmetric difference of sets `{p_{i−1}y}` and `{p_i y}`. So it is contained in
`{p_i y : 0 ≤ i ≤ ℓ}`.

**(3b) Doubling bound.** Every `h ∈ S` fixes `0` and `1` and has slopes at most `2`. So `h(t) ≤ 2t` and
`1 − h(t) ≤ 2(1 − t)`.

**(3c) Length.** Let `γ = t_1⋯t_ℓ` have product `δ_{1/2} = ({1/2}, e)`. By (3a), `p_i y = 1/2` for some `i`, and
`p_ℓ = e`.
- `p_i` is a product of `i` letters of `S`. By (3b), `1/2 ≤ 2^i y` in `Z_0` and `1/2 ≤ 2^i(1−y)` in `Z_1`.
- So `i ≥ log_2(1/(2y)) ≥ W + 1` in `Z_0` (since `log_2(1/(4y)) ≥ W`), and `i ≥ log_2(1/(2(1−y))) ≥ W + 2` in
  `Z_1`.
- The suffix `π(t_{i+1}⋯t_ℓ) = p_i^{−1}` sends `1/2` back to `y`, so its inverse sends `y` to `1/2`. The same bound
  gives `ℓ − i ≥ W+1` (resp. `W+2`).
- Hence `ℓ ≥ 2(W+1)` in `Z_0` and `ℓ ≥ 2(W+2)` in `Z_1`. More generally, a word for `δ_{y'}` in `T_y` has length at
  least twice the Schreier distance from `y` to `y'` in the generators `S`. ∎

## Step 4. The comparison constant

Put `X_t = Σ_u ν_{1/2}(u) ℓ_u N(t, γ_u)`, so `A = max_t X_t/ν_y(t)`.
- Since `Σ_t ν_y(t) = 1`, the maximum is at least the `ν_y`-average: `A ≥ Σ_t ν_y(t)·X_t/ν_y(t) = Σ_t X_t`.
- Also `Σ_t N(t, γ_u) = ℓ_u`, so `Σ_t X_t = Σ_u ν_{1/2}(u) ℓ_u²`.
- The atom `δ_{1/2}` has `ν_{1/2}(δ_{1/2}) = 2/20 = 1/10` (triples `(1,e,0)` and `(0,e,1)`).
- By Step 3, `A ≥ (1/10)·4(W+1)² = (2/5)(W+1)²` in `Z_0`, and `A ≥ (2/5)(W+2)²` in `Z_1`. ∎

(The lemma behind `A` is the standard path comparison: `E_{1/2}(f) = ½Σ_u ν_{1/2}(u)Σ_A|f(uA)−f(A)|²`, and
telescoping along `γ_u` with Cauchy–Schwarz gives `E_{1/2}(f) ≤ ½ Σ_t X_t Σ_B |f(tB) − f(B)|² ≤ A·E_y(f)`, as in
Step 3a of the gap route.)

## Step 5. Products

**Items 1 and 2.**
- In `Z_0`, the output is `A(1−r) ≥ (2/5)(W+1)² · 4/(5(2W+3)²) = 8(W+1)²/(25(2W+3)²)`. The ratio `(W+1)/(2W+3)`
  increases from `1/3` at `W = 0`, so the output is at least `8/225`.
- In `Z_1`, the output is at least `(2/5)(W+2)² · 8/(5(2W+3)²) = 16(W+2)²/(25(2W+3)²)`. The ratio
  `(W+2)/(2W+3)` decreases to `1/2`, so the output is at least `4/25`. ∎

**Item 3.** Let stage `i` transport from `y_{i−1}` to `y_i` with constant `A_i`, and let `d_i` be the Schreier
distance between them.
- By Step 3c and the argument of Step 4 with the atom `δ_{y_i}`, `A_i ≥ (2/5)d_i²`.
- The certified output is `A_k⋯A_1(1−r)`.
- By the triangle inequality, `Σ d_i ≥ d(y, 1/2) ≥ W+1` (resp. `W+2`), by Step 3c.
- *Claim.* If every `d_i ≥ 4`, then `Π_i (2/5)d_i² ≥ (2/5)(Σ_i d_i)²`.
  - The case `k = 1` is equality.
  - For the induction step, it suffices that `(2/5)X²·(2/5)d² ≥ (2/5)(X+d)²` for `X, d ≥ 4`, that is
    `√(2/5)·Xd ≥ X + d`.
  - Indeed `Xd ≥ 4·max(X,d)` and `X + d ≤ 2·max(X,d)`, and `4√(2/5) > 2.5 > 2`.
- So the product of constants is at least `(2/5)(W+1)²` (resp. `(2/5)(W+2)²`), and Step 5 applies unchanged. ∎

## Remark: why the endpoints (motivation only)

Let `y_k ∈ D` with `y_k → t ∈ [0,1]`, and let `H` be a Chabauty limit of `Stab_F(y_k)` along a subsequence.
- *If `t = 0`.* Each `g ∈ F` is linear near `0` with slope `2^j`. So `g` fixes all sufficiently small `y_k` iff
  `j = 0`. Hence `H = ker(g ↦ log_2 g'(0))` and `F/H ≅ Z`, which is recurrent. The case `t = 1` is symmetric.
- *If `t ∈ (0,1)`.* Every `g ∈ H` fixes infinitely many `y_k`, hence fixes `t` by continuity. By item 2 of
  `thompson-f-point-orbits-are-transient`, `F/H` is transient.

So the only recurrent localizations are the endpoint ones, and the claim shows they stall. This remark is not used in
Steps 1–5.

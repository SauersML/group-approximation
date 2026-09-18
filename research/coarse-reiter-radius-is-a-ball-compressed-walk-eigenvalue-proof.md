---
rg: 2
id: coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue-proof
kind: route
title: Bhattacharyya turns walk-averaged ℓ¹ displacement into one Rayleigh quotient, log-convexity of return moments picks a nearly Q-fixed vector, and squaring back gives coarse invariance
target: coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue
requires: []
artifacts:
  - experiments/ball-compressed-walk-spectra-2026-09-17/ball_spectra.py
  - experiments/ball-compressed-walk-spectra-2026-09-17/f_R9.json
  - experiments/ball-compressed-walk-spectra-2026-09-17/f2_R8.json
---

Notation is as in the claim. Inner products are real. `Q^t = Σ_g q_t(g) λ_g` has a nonnegative kernel, so for every
`η` we have `⟨|η|, Q^t|η|⟩ ≥ |⟨η, Q^t η⟩|`. Hence `ρ(r, t)` is attained at a nonnegative unit vector in `ℓ²(B_r)`.

**Step 1 (Bhattacharyya).** For probabilities `ν, ν'`, `Σ_x √(ν(x)ν'(x)) ≥ Σ_x min(ν(x), ν'(x)) = 1 − ‖ν − ν'‖/2`.
With `η = √ν` we have `λ_g η = √(gν)`, so `⟨η, λ_g η⟩ ≥ 1 − ‖gν − ν‖/2`.

**Step 2 (part (1)).** `WR(N) ≤ CR(N)`: a `ν` with `‖gν − ν‖ ≤ 1` on `B_N ⊇ supp q_N` has `Σ_g q_N(g)‖gν − ν‖ ≤ 1`.
`h(N) ≤ WR(N)`: if `ν ∈ P(B_r)` has `Σ_g q_N(g)‖gν − ν‖ ≤ 1`, then `η = √ν` is a unit vector of `ℓ²(B_r)` and, by
Step 1, `⟨η, Q^N η⟩ = Σ_g q_N(g)⟨η, λ_g η⟩ ≥ 1 − ½ Σ_g q_N(g)‖gν − ν‖ ≥ 1/2`. So `ρ(r, N) ≥ 1/2`.

**Step 3 (log-convexity, part (2)).** Let `η ≥ 0` be a unit vector in `ℓ²(B_r)` with `⟨η, Q^{2J} η⟩ ≥ a > 0`. Put
`c_j = ‖Q^j η‖₂² = ⟨η, Q^{2j} η⟩`. Then `c_0 = 1`, `c_J ≥ a`, and all `c_j > 0` for `j ≤ J` (they are nonincreasing
since `‖Q‖ ≤ 1`). By Cauchy–Schwarz and self-adjointness, `c_j² = ⟨Q^{j−1}η, Q^{j+1}η⟩² ≤ c_{j−1} c_{j+1}`, so the
ratios `c_j / c_{j−1}` are nondecreasing in `j`. Their product over `j = 1..J` is `c_J ≥ a`, so the last one satisfies
`c_J / c_{J−1} ≥ a^{1/J} ≥ 1 − δ` with `δ = ln(1/a)/J`.

Put `ζ = Q^{J−1} η`. It is nonnegative, nonzero, and supported in `B_{r+J−1}` because `Q` is supported on `B_1`. We
have `‖Qζ‖² ≥ (1 − δ)‖ζ‖²`. Since `0 ≤ Q ≤ I`, `Q − Q² ≥ 0`, so `⟨ζ, Qζ⟩ ≥ ‖Qζ‖² ≥ (1 − δ)‖ζ‖²`.

**Step 4 (from the quadratic form to every generator).** `⟨ζ, Qζ⟩ = ½‖ζ‖² + (2k)⁻¹ Σ_{s∈S'} ⟨ζ, λ_s ζ⟩`. So
`(2k)⁻¹ Σ_{s∈S'} (‖ζ‖² − ⟨ζ, λ_s ζ⟩) ≤ δ‖ζ‖²`. Each summand is `≥ 0` by Cauchy–Schwarz, so each is at most
`2kδ‖ζ‖²`, and `‖λ_s ζ − ζ‖² = 2(‖ζ‖² − ⟨ζ, λ_s ζ⟩) ≤ 4kδ‖ζ‖²` for every `s ∈ S'`.

**Step 5 (square back).** Put `μ = ζ²/‖ζ‖²`, a probability on `B_{r+J−1}`. Then `sμ = (λ_s ζ)²/‖ζ‖²` and
`‖sμ − μ‖ = ‖(λ_sζ − ζ)(λ_sζ + ζ)‖₁/‖ζ‖² ≤ ‖λ_sζ − ζ‖·‖λ_sζ + ζ‖/‖ζ‖² ≤ 2√(4kδ) = 4√(kδ)`.
For a word `g = s_1 ⋯ s_ℓ`, the triangle inequality and isometry of translations give
`‖gμ − μ‖ ≤ 4|g|√(k ln(1/a)/J)`. This is `≤ 1` on `B_M` as soon as `J ≥ 16kM² ln(1/a)`, so `CR(M) ≤ r + J − 1`.
That is part (2).

**Step 6 (part (3)).** The first two inequalities are Step 2. For the third, let `r = h(2J_M)`. By the opening remark
there is a unit `η ≥ 0` on `B_r` with `⟨η, Q^{2J_M} η⟩ ≥ 1/2`. Step 3–5 with `a = 1/2` and `J = J_M ≥ 16kM² ln 2`
give `CR(M) ≤ r + J_M`. The last inequality is Step 2 at window `2J_M`. ∎

**Step 7 (the Corollary).** Two facts are used.
- *`R(m) ≥ m` in an infinite group.* If `ν ∈ N_{m,n}` exists, some `x` has `B_m x ⊆ B_n`, so `|B_m| ≤ |B_n|`. Spheres
  of an infinite finitely generated group are nonempty, so ball sizes strictly increase, and `n ≥ m`.
- *Tower slack.* Put `c = 32k ln 2 + 2`, so `2J_N ≤ cN²` and `J_N ≤ cN²`. Choose `D = D_k` with
  `exp_D(x) ≥ cx² + x` for all integers `x ≥ 1` (for `k ≤ 5`, `D = 4` works because `exp_4(1) = 65536`). For every
  `E ≥ 0` and `y ≥ 1`, `exp_E` is increasing with slope `≥ 1` on integers, so
  `exp_{E+D}(y) − exp_E(y) ≥ exp_D(y) − y ≥ cy²`.

*RGAP₁ ⇒ SGAP₁.* Fix `E`. Apply RGAP₁ with `E + D`: some `N` has `CR(N) > exp_{E+D}(y)` with
`y = R(exp_{E+D} N) ≥ N`. Put `N' = 2J_N ≤ cN²`. By (3), `h(N') ≥ CR(N) − J_N > exp_{E+D}(y) − cy² ≥ exp_E(y)`.
Since `exp_{E+D}(N) ≥ exp_E(cN²) ≥ exp_E(N')` and `R` is nondecreasing (a set that is Ramsey for `B_{m'}` is Ramsey for
`B_m ⊆ B_{m'}`), `y ≥ R(exp_E N')`. So `h(N') > exp_E(R(exp_E N'))`. That is, `ρ(n, N') < 1/2` at
`n = exp_E(R(exp_E N'))`, which is SGAP₁ at `E`.

*SGAP₁ ⇒ RGAP₁.* Immediate from `h(N) ≤ CR(N)`.

*WGAP₁.* The same two arguments with `WR` in place of `h`, using `WR(N) ≤ CR(N) ≤ WR(2J_N) + J_N` from (3). ∎

**Step 8 (the free-group calibration quoted in the claim).** By Kesten, `‖Σ_{s∈S} λ_s‖ = 2√3` in `F_2` with four
free generators and inverses, so `‖P‖ = (1 + 2√3)/5` and `‖Q‖ = (6 + 2√3)/10 < 0.9465`. Then
`ρ(r, N) ≤ ‖Q^N‖ = ‖Q‖^N < 0.489 < 1/2` for `N ≥ 13` and every `r`, so `h_{F_2}(N) = ∞`. The ℓ¹ balance of walk laws is
the standard estimate `‖q_{L+1} − q_L‖ = O(L^{−1/2})` for a lazy walk (true in every group). This only illustrates that
time-shift pairs carry no amenability information and is not used in Steps 1–7.

**Step 9 (data).** `ball_spectra.py` builds `B_R` exactly (Thompson's `F` as PL maps with rational breakpoints;
`F_2` as reduced words), checks ball sizes (`F`: 1, 5, 17, 53, 161, 475, 1381, 3957, 11237, 31589), and computes
`ρ(n, t)` for `n + t ≤ R` by Lanczos on `Π_n Q^t Π_n`. Only `B_{n+t}` is needed. Sanity values: `ρ(0,1) = 0.6` and
`ρ(0,2) = 0.4` in both groups. The outputs are in `f_R9.json` and `f2_R8.json`. They are floating point and are used
only as calibration, not in any proof.

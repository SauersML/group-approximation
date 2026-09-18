---
rg: 2
id: thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap-proof
kind: route
title: Bound Ramsey sets by one coarse measure, smooth the coarse measure spectrally for fine precision, and recover coarse measures from two fine Ramsey calls through Towsner's Proposition 3.1
target: thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap
requires: [coarse-ball-invariance-gives-fine-reiter-measures, moore-ramsey-criterion-for-amenability]
---

Notation is as in the claim. `S' = {e, x_0^{±1}, x_1^{±1}}`, so `|S'| = 5`, and `|B_m| ≤ 2·3^m − 1 ≤ 5^m`.
`gν(f) = Σ_x (gν)(x) f(x)`.

**Balancing fact.** If `Σ_x c_x = 0` and `f : G → [0,1]`, then `|Σ_x c_x f(x)| ≤ ‖c‖₁/2`, because the sum lies between
the negative mass and the positive mass of `c`, and each of these is `‖c‖₁/2` in absolute value.

**(a).** Let `ν` witness `CR(2m) = r`. Then `B_m·supp ν ⊆ B_{r+m}`, so `P(B_m)ν ⊆ P(B_{r+m})`. Take `E ⊆ B_{r+m}` and
`μ, μ' ∈ P(B_m)`. Then `μν − μ'ν = Σ_{g,g'} μ(g)μ'(g')(gν − g'ν)` and
`‖gν − g'ν‖ = ‖g'^{−1}gν − ν‖ ≤ 1`, since `g'^{−1}g ∈ B_{2m}`. By the balancing fact,
`|μν(E) − μ'ν(E)| ≤ 1/2`. So `B_{r+m}` is 1/2-Ramsey with respect to `B_m`. (If `CR(2m) = ∞` there is nothing to prove.)

**(b), first inequality.** Let `ν ∈ P(B_n)` witness `F(m, ε)`, so `P(B_m)ν ⊆ P(B_n)` and `Σ_{g∈B_m}‖gν − ν‖ < ε`.
For any `f : B_n → [0,1]` and `g ≠ g'` in `B_m`, the balancing fact gives
`|gν(f) − g'ν(f)| ≤ (‖gν − ν‖ + ‖g'ν − ν‖)/2 < ε`. So `R̃(m, ε) ≤ F(m, ε)`.

**(b), second inequality.** Let `r = CR(2K)`, witnessed by `ν`. Apply `coarse-ball-invariance-gives-fine-reiter-measures`
to get `μ` supported in `B_{r+K−1}` with `‖gμ − μ‖ ≤ 10|g|√(2 ln 2/K)`. Put `n = r + K − 1 + m`, so
`P(B_m)μ ⊆ P(B_n)`. Then

`Σ_{g∈B_m}‖gμ − μ‖ ≤ 10 m |B_m| √(2 ln 2/K) < 1/u`

because `K > 200 ln 2 · m² 25^m u² ≥ 200 ln 2 · m² |B_m|² u²`. So `F(m, 1/u) ≤ n ≤ CR(2K) + K + m`.

**(b), size of K.** `m²/10.24^m ≤ 1/10.24` for `m ≥ 1`, and `u²/2^{8u} ≤ 1/256` for `u ≥ 1`. Hence
`2K ≤ 278 m² 25^m u² + 2 ≤ 0.11·2^{8(m+u)} + 2 ≤ 2^{8(m+u)}`. For `x ≥ 2` we have `2^{2^x} ≥ 8x`
(equality `16 = 16` at `x = 2`, and the left side grows faster after that), so `2^{8x} ≤ 2^{2^{2^x}} = exp_3(x)`. With `x = m + u ≥ 2`
this gives `2K ≤ exp_3(m+u)`.

**(c).** Let `ν ∈ P(B_n)` witness `F(1, 1/M)`. Each generator `s` has `‖sν − ν‖ < 1/M`, and so does `s⁻¹`, since
`‖s⁻¹ν − ν‖ = ‖ν − sν‖`. Translation is an ℓ¹ isometry, so `‖gν − ν‖ < M·(1/M) = 1` for `g ∈ B_M`. Hence
`CR(M) ≤ n`. Proposition 3.1 with `|S| = 2` and `ε = 1/(4M)` gives `F(1, 1/M) ≤ R̃(1, 1/(4M), 2)`. Towsner's
inequality with `l = 2` gives the last bound.

**Two growth facts.** `F` is infinite, so `R(N) ≥ N` (see `moore-ramsey-criterion-for-amenability`). For `z ≥ 2`,
`2z ≤ 2^z`. Every function involved is nondecreasing in the relevant argument: `R`, `CR` and `exp_D` directly,
and `R̃(·, ε)` because shrinking `B_m` weakens the requirement.

**Corollary 1.** Assume CRE(E). Fix `m, u ≥ 1` and let `K = K_{m,u}`. By (b), monotonicity and CRE(E),

`R̃(m, 1/u) ≤ CR(exp_3(m+u)) + K + m ≤ exp_E(y) + K + m`, with `y = R(exp_{E+3}(m+u))`.

If `y = ∞` the claim is trivial. Otherwise `y ≥ exp_{E+3}(m+u) ≥ exp_3(m+u) ≥ 2K ≥ K + m`, because `K ≥ 139 m² ≥ m`.
So the bound is at most `exp_E(y) + y ≤ 2 exp_E(y) ≤ exp_{E+1}(y)`, using `exp_E(y) ≥ y ≥ 2`. Finally,
`exp_{E+1}(y) ≤ exp_{E+3}(R(exp_{E+3}(m+u)) + u)`. This is AMP(E+3).

**Corollary 2.** Assume AMP(D) and fix `M ≥ 1`. Put `ε = 1/(4M)` and `u = 4M`. AMP(D) at `m = 1` gives
`R̃(1, ε) ≤ A_M`. `R̃(1, ε) ≥ 1`, since `B_1 x ⊆ B_n` forces `n ≥ 1`. So AMP(D) applies at `m = R̃(1, ε)` (if this is `∞`,
then `A_M = ∞` and there is nothing to prove). With (c) and monotonicity of `R` and `exp_D`, it gives

`CR(M) ≤ R̃(R̃(1, ε), ε) ≤ exp_D(R(exp_D(R̃(1, ε) + 4M)) + 4M) ≤ exp_D(R(exp_D(A_M + 4M)) + 4M)`.

**Corollary 3.**
- ¬AMP ⇒ RGAP₁. Fix `E` and take `D = E + 3`. By ¬AMP, AMP(D) fails. By Corollary 1, CRE(E) fails, so some `N` has
  `CR(N) > exp_E(R(exp_E(N)))`.
- RGAP₂ ⇒ ¬AMP. Fix `D`. RGAP₂ gives an `M` violating the conclusion of Corollary 2, so AMP(D) fails.
- Each statement implies amenability. A strict inequality `X > Y` in `[0, ∞]` forces `Y < ∞`, so `R` is finite at
  arguments `≥ exp_E(1)` (respectively `≥ exp_D(1)`) for every `E` (respectively `D`). `R` is nondecreasing, so
  `R < ∞` everywhere, and Moore's Theorem 1.3 (2)⇒(4) applies. ∎

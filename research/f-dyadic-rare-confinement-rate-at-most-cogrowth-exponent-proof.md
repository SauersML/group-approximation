---
rg: 2
id: f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent-proof
kind: route
title: Koopman compression to the cylinder, confined walks on Cayley balls, Walsh levels and dyadic depth
target: f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent
requires: [thompson-f-norm-bound-from-hhr-exact-moments, kesten-amenable-stabilizer-uniform-gap, f-dyadic-ea-iff-inverted-orbit-confinement, thompson-f-amenable-iff-dyadic-action-extensively-amenable]
artifacts:
  - experiments/f-dyadic-rare-confinement-2026-09-17/cloning.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_long.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/psl_return.py
---

Notation as in the target. For `g ∈ G` and `A ⊆ Ω`, `gA = {gω : ω ∈ A}`, so `π(g)1_A = 1_{gA}`. Symmetry of
`μ` makes `P` self-adjoint, and `‖P‖ ≤ 1`. The operators `P` and `Q = 1_E P 1_E` are *positivity preserving*,
and `|Qf| ≤ Q|f|` pointwise. Hence `|⟨Qf,f⟩| ≤ ⟨Q|f|,|f|⟩`, and

`‖Q‖ = sup{⟨Qf,f⟩ : f ≥ 0, ‖f‖ = 1} = max spec Q`.   (P0)

The same holds for `P` on any permutation module.

## 1. Koopman identity

1. By induction on `n`,
   `Q^n 1_E = Σ μ(h_1)⋯μ(h_n) 1_{E ∩ h_nE ∩ h_nh_{n−1}E ∩ ⋯ ∩ h_n⋯h_1E}`.
   This uses `1_E π(h) 1_B = 1_{E ∩ hB}` and `h(B ∩ B') = hB ∩ hB'`.
2. Since `gE = {ω : ω(gx_0) = 0}`, the intersection is the event that `ω` vanishes on
   `{h_n⋯h_k x_0 : 1 ≤ k ≤ n+1} = g_n{g_{k−1}⁻¹x_0 : 1 ≤ k ≤ n+1} = g_n O_n`, a set of cardinality `|O_n|`.
   So `⟨Q^n 1_E, 1_E⟩ = E m(ω|_{g_nO_n} = 0) = E 2^{−|O_n|}`.
3. **Upper bound.** `E 2^{−|O_n|} ≤ ‖Q‖^n ‖1_E‖² = ‖Q‖^n/2`.
4. **Lower bound.**
   - Fix `r < ‖Q‖`. The spectral projection `Π = 1_{(r,‖Q‖]}(Q)` is nonzero by (P0).
   - Bounded nonnegative functions supported in `E` span a dense subspace of `L²(E)`. So some such `f`,
     with `0 ≤ f ≤ c1_E`, has `Πf ≠ 0`.
   - `Q^{2n}` preserves positivity, so `⟨Q^{2n}f,f⟩ ≤ c²⟨Q^{2n}1_E,1_E⟩`.
   - By the spectral theorem, `⟨Q^{2n}f,f⟩ ≥ r^{2n}‖Πf‖²`.
   - Hence `liminf (E 2^{−|O_{2n}|})^{1/2n} ≥ r`.
5. **Odd times.** `|O_n|` is nondecreasing in `n`, so `E 2^{−|O_n|}` is nonincreasing. The even-time limit
   therefore controls odd times, and `lim −(1/n) log E 2^{−|O_n|} = −log ‖Q‖`.

## 2. Cylinder almost-invariant sets

For `f ∈ L²(E)` with `‖f‖ = 1`: `⟨Pf,f⟩ = 1 − ½ Σ_h μ(h)‖π(h)f − f‖²`.

- **(⇐)** If `A ⊆ E` and `Σ μ(h) m(hAΔA) ≤ ε m(A)`, then
  `⟨Q1_A,1_A⟩ = Σ μ(h) m(hA∩A) ≥ (1−ε/2) m(A)`. So `‖Q‖ ≥ 1−ε/2`.
- **(⇒)** If `‖Q‖ = 1`, then by (P0) there are `f ≥ 0` in `L²(E)` with `‖f‖ = 1` and
  `Σ μ(h)‖π(h)f−f‖² ≤ δ²`.
  1. Put `u = f²` and `A_t = {u > t} ⊆ E`.
  2. By Cauchy–Schwarz, `Σ μ(h)‖π(h)u − u‖_1 ≤ Σ μ(h)‖π(h)f−f‖_2 ‖π(h)f+f‖_2 ≤ 2δ`.
  3. By the layer-cake formula, `‖π(h)u−u‖_1 = ∫_0^∞ m(hA_t Δ A_t) dt` and `∫_0^∞ m(A_t) dt = 1`.
  4. Hence `∫ (Σ μ(h) m(hA_tΔA_t) − 2δ m(A_t)) dt ≤ 0`, so some `t` has `m(A_t) > 0` and
     `Σ μ(h) m(hA_tΔA_t) ≤ 2δ m(A_t)`.

## 3. Cogrowth upper bound

1. **The killed walk.** Let `B_R` be the ball of radius `R` in the word metric of `supp μ`, and `P_R` the
   restriction of the kernel `p(g, hg) = μ(h)` to `B_R`.
   - It is a finite, symmetric, nonnegative matrix.
   - It is irreducible: if `g = s_1⋯s_r` with `r ≤ R`, left multiplication by `s_1⁻¹, s_2⁻¹, …` walks to `e`
     inside `B_R`.
2. **Perron–Frobenius.** Let `λ_R` be the Perron eigenvalue and `φ_R > 0` a unit Perron eigenvector. Then
   `P_R^{2n}(e,e) = Σ_j θ_j^{2n} ψ_j(e)² ≥ λ_R^{2n} φ_R(e)²`.
3. **Confined walks give the bound.** `P(g_1,…,g_{2n} ∈ B_R) ≥ P_R^{2n}(e,e)`. On that event
   `g_i⁻¹ ∈ B_R` (the ball is symmetric), so `O_{2n} ⊆ B_R x_0` and `|O_{2n}| ≤ |B_R|`. Hence
   `E 2^{−|O_{2n}|} ≥ 2^{−|B_R|} φ_R(e)² λ_R^{2n}`, and by §1, `‖Q‖ ≥ λ_R`.
4. **Limit in `R`.**
   - `λ_R = max{⟨Pf,f⟩ : supp f ⊆ B_R, ‖f‖ = 1}` for `P = λ(μ)` on `ℓ²(G)`. This is nondecreasing in `R`.
   - Its supremum over `R` is `max spec λ(μ) = ‖λ(μ)‖ = ρ`, by (P0) and density of finitely supported
     functions.
   - So `‖Q‖ ≥ ρ`, i.e. `Λ ≤ −log ρ`.
5. **Numerical value for F.** `thompson-f-norm-bound-from-hhr-exact-moments` gives `ρ > 0.901532` for `μ`
   uniform on `{x_0^{±1},x_1^{±1}}`. So `Λ_F ≤ 0.10366`.

## 4. Toggle lower bound and squeeze

1. **Walsh basis.** The characters `w_A(ω) = Π_{x∈A}(−1)^{ω(x)}`, for finite `A ⊆ X`, form an orthonormal
   basis of `L²(Ω)`, with `π(g)w_A = w_{gA}`. So `L²(Ω) = C1 ⊕ L²_0`, where `L²_0 = ⊕_{k≥1} ℓ²(P_k(X))` is
   `P`-invariant.
2. **Decompose.** Take `f ∈ L²(E)` with `‖f‖ = 1`, and write `f = c1 + f_0`, where `c = ⟨f,1⟩ = ⟨f,1_E⟩`.
   By Cauchy–Schwarz, `|c|² ≤ ‖1_E‖² = 1/2`.
3. **Estimate.** `⟨Qf,f⟩ = ⟨Pf,f⟩ = |c|² + ⟨Pf_0,f_0⟩ ≤ |c|² + ρ_0^+(1−|c|²) ≤ (1+ρ_0^+)/2`, because
   `ρ_0^+ ≤ 1`. By (P0), `‖Q‖ ≤ (1+ρ_0^+)/2`.
4. **Amenable stabilizers.**
   - `ℓ²(P_k(X))` is the direct sum over `G`-orbits `G·A` of the quasi-regular representations
     `ℓ²(G/Stab_G(A))`.
   - If every `Stab_G(A)` is amenable and `μ` is uniform on a finite symmetric generating `S`, then
     `kesten-amenable-stabilizer-uniform-gap` (route `kesten-amenable-stabilizer-gap-citation`) gives norm
     at most `ρ(G,S)` on each summand. It cites: "Induction preserves weak containment, and `H` amenable
     gives `1_H` weakly contained in `lambda_H`", so `‖M‖ ≤ rho(A,S)`.
   - So `ρ_0^+ ≤ ρ`. Combined with §3, `−log((1+ρ)/2) ≤ Λ ≤ −log ρ`.
5. **Vanishing.** `Λ = 0` iff `ρ = 1` iff `G` is amenable (Kesten, *Symmetric random walks on groups*,
   Trans. AMS 92 (1959) 336–354).
6. **Calibrators.**
   - `PSL_2(Z) ↷ P¹(Q)`: the stabilizer of `∞` is `{[[1,n],[0,1]]} ≅ Z`. Every finite-set stabilizer
     contains a pointwise stabilizer (a subgroup of a conjugate of `Z`) with finite index, so it is amenable.
     `PSL_2(Z)` contains free subgroups, so `ρ < 1` and `Λ_PSL > 0`.
   - Free actions: stabilizers are trivial. This gives the squeeze for `F_2`, and `Λ = 0` for amenable
     groups by §3.

## 5. Every Walsh level of F has top spectrum 1

1. Let `R_N = {2^{−1},…,2^{−N}} ⊂ D` and `Φ_N = P_k(R_N)` with `N ≥ k`.
2. **Generator action on the ray.**
   - `x_1` is the identity on `[0,1/2]`, so `x_1^{±1}Φ_N = Φ_N`.
   - `x_0(t) = t/2` on `[0,1/2]`, so `x_0 Φ_N = P_k({2^{−2},…,2^{−N−1}})` and
     `|x_0Φ_N \ Φ_N| = binom(N−1,k−1)`.
   - Likewise `|x_0⁻¹Φ_N \ Φ_N| = binom(N−1,k−1)`: `x_0⁻¹` maps `2^{−j} ↦ 2^{−j+1}` for `j ≥ 2`, and
     `1/2 ↦ 3/4`.
3. **Rayleigh quotient.** With `f = 1_{Φ_N}`,
   `⟨Pf,f⟩/‖f‖² = Σ_h μ(h)|hΦ_N ∩ Φ_N|/|Φ_N| ≥ 1 − binom(N−1,k−1)/binom(N,k) = 1 − k/N → 1`.
   Hence `ρ_k = 1` for every `k ≥ 1`, and the bound of §4 is vacuous for `F`.
4. **Stabilizers.** For finite `A ⊂ D`, the setwise stabilizer contains the elements supported in an
   interval `[a,b]` of dyadics disjoint from `A`, i.e. a copy of `F`. So the hypothesis of §4.4 is not
   available.

## 6. Band completeness for F

1. **Killed chain.** `O_n ⊆ D_C` ⟺ `g_i⁻¹(1/2) ∈ D_C` for all `i ≤ n` ⟺ `1/2 ∈ g_iD_C = T_i` for all
   `i ≤ n`. Also `T_i = h_iT_{i−1}`, so `(T_i)` is a Markov chain and the band probability is its survival.
2. **Upper bound.** `D_C ⊆ D_{C+1}`, so `λ_C` is nondecreasing. On the event `O_n ⊆ D_C` we have
   `2^{−|O_n|} ≥ 2^{−(2^C−1)}`, so `P(O_n ⊆ D_C) ≤ 2^{2^C} E 2^{−|O_n|}`. By §1, `λ_C ≤ ‖Q‖`.
3. **Dyadic depth.** Let `d(t) = min{C : t ∈ D_C}`. From the piecewise formulas
   - `x_0`: `t/2`, `t−1/4`, `2t−1`;
   - `x_0⁻¹`: `2t`, `t+1/4`, `(t+1)/2`;
   - `x_1`: `t`, `t/2+1/4`, `t−1/8`, `2t−1`;
   - `x_1⁻¹`: `t`, `2t−1/2`, `t+1/8`, `(t+1)/2`,

   each generator `s` satisfies `d(st) ≤ max(d(t),2) + 1`. Starting from `d(1/2) = 1`, it follows that
   `d(g·1/2) ≤ |g| + 2` for `|g| ≥ 1`, so `B_R·(1/2) ⊆ D_{R+2}`.
4. **Lower bound.** By §3, `P(O_{2n} ⊆ D_{R+2}) ≥ P(g_1,…,g_{2n} ∈ B_R) ≥ φ_R(e)² λ_R^{2n}`. So
   `λ_{R+2} ≥ λ_R ↑ ρ(F,μ)`.
5. **Chain of equivalences.**
   - `F` amenable ⟹ `ρ = 1` (Kesten) ⟹ `sup_C λ_C = 1`.
   - `sup_C λ_C = 1` ⟹ `‖Q‖ = 1`, i.e. `Λ_F = 0` (step 2).
   - `Λ_F = 0` ⟹ `F ↷ D` extensively amenable, by condition 2 of `f-dyadic-ea-iff-inverted-orbit-confinement`.
   - Extensively amenable ⟹ `F` amenable, by `thompson-f-amenable-iff-dyadic-action-extensively-amenable`.

## Numerics

- `cloning.py` checks the two relators of `F` on its generator maps and that `x_0, x_1` do not commute.
- `cloning.py`, `band_long.py` and `lambda_long.py` run population dynamics for the chains of §1 and §6.
- `psl_return.py` computes exact return probabilities on `PSL_2(Z)`.

Runtimes are stated in each docstring (at most about 15 minutes per model). No numerical output is used in
§1–§6.

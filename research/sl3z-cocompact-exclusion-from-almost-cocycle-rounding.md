---
rg: 2
id: sl3z-cocompact-exclusion-from-almost-cocycle-rounding
kind: route
title: Round the labels of a weak-containment model to flat ones, kill the holonomy by Bass-Milnor-Serre, and price the repair by norm drift
target: sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions
requires:
  - sl3z-lambda-almost-cocycles-round-to-flat-ones
  - sl3z-cocompact-microstates-carry-flat-lambda-labels
  - sl3-norm-drift-excludes-finite-almost-invariant-configs
  - bms-sln-z-representations-agree-with-algebraic-ones
---

Conditional route. Notation as in `sl3z-cocompact-microstates-carry-flat-lambda-labels`: `G = SL_3(R)`,
`Γ = SL_3(Z)`, `X = G/Λ` with (R), a compact `F ⊆ G` with `FΛ = G` and `C_F = max_(f ∈ F) max(||f||, ||f^(−1)||)`,
and scale `ε < ε_0` with `η(ε) < κ/24`.

Suppose the claim fails: there are finite `Γ`-sets `V_k` and marks `y_k` with a proportion `θ_k → 0` of bad
pairs at scale `ε`. Average over orbits and keep a transitive `V = V_k` whose proportion of bad pairs is
at most `θ = θ_k`. Lift `y(v) = g_vΛ` with `g_v ∈ F`.

1. **Bounded labels, few defects.** Labels `λ(v,s)` (item 1 of the flat-labels claim, minimizers on bad
   pairs) lie in the finite set `Σ = Λ ∩ F^(−1) S B F`, where `B` is the closed `diam(X)`-ball at `1`.
   By item 2, a non-flat cell contains a bad pair. Each pair lies in at most `L·|R|` cells, so there are at
   most `δ|V|` non-flat cells, with `δ = 12 L |R| θ`.
2. **Rounding.** DTR gives a flat `λ'` with at most `f_Σ(δ)|V|` changed pairs and log-norm budget at most
   `f_Σ(δ)|V|` on them.
3. **Finite holonomy.** `λ'` is flat, so `Γ` acts on `Ω = V × Λ` by `(v,μ) ↦ (sv, λ'(v,s)^(−1)μ)`, and the stabilizer of
   `(v,1)` is the kernel of a homomorphism `ρ_v : Γ_v → Λ` (item 3). By Step 5 of
   `sl3z-cocompact-not-factor-of-bernoulli-times-profinite-proof` (Bass--Milnor--Serre and (R)), `ρ_v` has
   finite image. So every `Γ`-orbit on `Ω` is finite. Let `O` be the union of the orbits meeting `V × {1}`. Each
   `σ̃'_s` maps the fibre `O_v` bijectively onto `O_(sv)`, and `V` is transitive, so all fibres have one size `m`.
4. **Pricing.** Put `Φ(v,μ) = g_vμ` and `N = log||Φ||`. Call `(v,s)` *repaired* if it is bad for `y` or
   `λ' != λ` there. On unrepaired pairs, `N(σ̃'_s ω) >= log||sΦ(ω)|| − η(ε)`. On every pair, since
   `Φ(σ̃'_s ω) = (g_(sv)λ'^(−1)g_v^(−1)s^(−1))·sΦ(ω)`,

   ```text
   N(σ̃'_s ω)  >=  log||sΦ(ω)|| − log||s g_v λ'(v,s) g_(sv)^(−1)||  >=  log||sΦ(ω)|| − b_1 − log||λ'(v,s)||,
   ```

   with `b_1 = log(max_s ||s||) + 2 log C_F`. The badness of `((v,μ),s)` depends only on `(v,s)`, and each `(v,s)`
   occurs `m` times in `O × S`.
5. **Drift.** Bijectivity gives `Σ_(ω ∈ O) Σ_s [N(σ̃'_s ω) − N(ω)] = 0`. By Lemma 2.1 of the drift claim,
   `Σ_s [log||sΦ(ω)|| − N(ω)] >= κ`. Dividing by `m|V|`,

   ```text
   κ  <=  12 η(ε) + (1/|V|) Σ_(repaired (v,s)) ( b_1 + log||λ'(v,s)|| )  <=  12 η(ε) + b_1 (12θ + f_Σ(δ)) + f_Σ(δ).
   ```

   For unchanged bad pairs, `λ' = λ ∈ Σ` and `log||λ|| <= b_Σ`. Absorb that into `b_1`. As `k → ∞`, `θ → 0` and
   `f_Σ(δ) → 0`, so the right side tends to `12η(ε) < κ/2`. Contradiction. ∎

So for fixed `ε` the proportion of bad pairs is bounded below, which is the claim with `ε_0 = ε` and some
`θ_0 > 0`. The equivalent forms follow as in that node.

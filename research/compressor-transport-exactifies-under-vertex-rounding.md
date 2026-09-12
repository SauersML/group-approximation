---
rg: 2
id: compressor-transport-exactifies-under-vertex-rounding
kind: claim
title: Under vertex rounding, property (T) makes the compressor transport an exact intertwiner on a large subrepresentation
distinct_from:
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that bounds the commutant excess by non-unit congruence mass; this proves that the rounded vertex representation and its compressor transport are exactly equivalent off a small trace, which turns the ultralimit invariance of root spectra into total-variation invariance at each finite stage.
  vertex-rounding-reduces-ccr-to-commutant-excess: that reduces (CCR) to the finite excess eps_n under (H1); this is a transport lemma on the rounded representations themselves, with no commutant statement.
artifacts:
  - research/artifacts/nh-unit-type-rounding-2026-09-12.md
---

**ESTABLISHED.** Setup:
- `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`, the explicit Theorem E pair.
- `A ∈ SL_d(Z)` a compressor with all entries `>= 1`. `φ_A` is the substitution `x^a -> x^(Aa)`.
- `κ` is the Kazhdan constant of `(Γ, F_Γ)`.
- `σ : G -> U(prod_U M_n)` is trace-preserving.
- Genuine representations `π_n : Γ -> U(n')`, with `n'/n -> 1`, round `σ_n` on `F_Γ`, i.e. (H1).
- Put `ρ_n = π_n ∘ Ad A`, and let `δ_n` be the `F_Γ`-intertwining defect of a unitary representative of `σ_n(A)` between `π_n` and `ρ_n`.

Then:
1. `δ_n -> 0` along `U`.
2. There are `π_n(Γ)`-invariant `Q` and `ρ_n(Γ)`-invariant `Q'` with `τ(1 - Q) = τ(1 - Q') <= 4δ_n^2/κ^2`, and a partial isometry
   `W : Q -> Q'` with `W π_n(γ) = ρ_n(γ) W`.
3. For each root subgroup, e.g. `e_12`, let `μ_n` be the normalized spectral measure of
   `f -> π_n(e_12(f))`, and `D_A χ = χ ∘ φ_A`. Then

   ```text
   | μ_n(E) - μ_n(D_A^(-1) E) |  <=  4 δ_n^2 / κ^2      for every Borel E.
   ```

**Reading.** Torus invariance of the ultralimit is weak* only. Property (T) upgrades the compressor
direction to total-variation invariance at every finite stage, uniform over all test sets. No claim
about the actor `G` beyond `σ(A)` is used. Derivation: `compressor-transport-exactifies-proof`.

---
rg: 2
id: cantor-central-witnesses-have-long-range-dependence-proof
kind: route
title: "Two prefix moves turn independence of two cone phases into ν ≈ ν * ν in total variation; the Fourier transform of such a law cannot leave 1, so both halves carry an atom at 0 and the central phase vanishes"
target: cantor-central-witnesses-have-long-range-dependence
requires: []
---

Notation is as in the target. `e(x) = e^{2πix}` on `T`. `ν̂(m) = ∫ e(mx) dν(x)`. `ν_w` is the
law of `χ[w]`. Push-forwards and marginals do not increase `d`, and
`d(P⊗Q, P'⊗Q') ≤ d(P,P') + d(Q,Q')`.

## 1. Atom lemma

**Lemma 1.** Let `ν` be a probability on `T`, `0 < κ ≤ 1/4`, `d(ν, ν*ν) ≤ κ/2`, and
`η = ∫ |e(x) − 1| dν < 1 − 4κ`. Then `ν({0}) ≥ 1 − 2κ`.

*Proof.*
- For every `m`: `|ν̂(m) − ν̂(m)²| = |∫ e(mx) d(ν − ν*ν)| ≤ 2d(ν, ν*ν) ≤ κ`.
- *Dichotomy.* If `|z| ≤ 1` and `|z||1 − z| ≤ κ`, then `z ∈ D_0 = {|z| ≤ 2κ}` or
  `z ∈ D_1 = {|1 − z| ≤ 2κ}`. If `|z| ≤ 1/2` then `|1 − z| ≥ 1/2`, so `|z| ≤ 2κ`. Otherwise
  `|1 − z| ≤ 2κ`. For `z ∈ D_0` and `w ∈ D_1`, `|z − w| ≥ 1 − |z| − |1 − w| ≥ 1 − 4κ`.
- *Steps.* `|ν̂(m+1) − ν̂(m)| ≤ ∫ |e((m+1)x) − e(mx)| dν = η < 1 − 4κ`.
- *Induction.* `ν̂(0) = 1 ∈ D_1`. If `ν̂(m) ∈ D_1`, then `ν̂(m+1)` lies within `η` of it, so it
  is not in `D_0`, hence in `D_1`. So `Re ν̂(m) ≥ 1 − 2κ` for all `m ≥ 0`.
- *Atom.* `F_M(x) = M^{-1} Σ_{m<M} e(mx)` satisfies `|F_M| ≤ 1`, and `F_M(x) → 1[x = 0]`
  pointwise on `T`. By dominated convergence,
  `ν({0}) = lim_M M^{-1} Σ_{m<M} Re ν̂(m) ≥ 1 − 2κ`. ∎

## 2. Fibrewise total variation

**Lemma 2.** Let `f : Â → Y` be `V`-invariant Borel and `μ = ∫ μ_y dρ(y)` its disintegration.
Then `d(k_*μ, μ) = ∫ d(k_*μ_y, μ_y) dρ(y)` for every `k ∈ V`.

*Proof.*
- `Â` is compact metrizable since `A` is countable, so the disintegration exists.
- `f∘k = f`, so `k_*μ_y` is concentrated on `f^{-1}(y)`, and `k_*μ = ∫ k_*μ_y dρ` is a
  disintegration of `k_*μ` along `f`, with the same marginal `ρ`.
- Let `τ = (μ + k_*μ)/2`, with `μ = pτ` and `k_*μ = qτ`, and disintegrate `τ = ∫ τ_y dρ`.
  Then `∫ (pτ_y) dρ` is a disintegration of `μ`, since `f_*μ = ρ` forces `∫ p dτ_y = 1` for
  `ρ`-a.e. `y`. By uniqueness, `μ_y = pτ_y` and `k_*μ_y = qτ_y` a.e.
- So `d(k_*μ, μ) = ½∫|p − q| dτ = ∫ ½∫|p − q| dτ_y dρ = ∫ d(k_*μ_y, μ_y) dρ`. ∎

## 3. One fibre

Fix `y` and write `μ_y = μ'`. Let `ε_k = d(k_*μ', μ')` for `k ∈ F`, `ε' = Σ_k ε_k`,
`α = α_y` and `η' = ∫ |e(χ[0]) − 1| dμ'`.

**Lemma 3.** `μ'(χ[C] ≠ 0) ≤ η' + 25ε' + 8α`.

*Proof.*
- *Moves.* `(k·χ)[U] = χ[k^{-1}U]`.
  - `g^{-1}[00] = [u]` and `g^{-1}[01] = [v]`, so the law of `(χ[00], χ[01])` under `g_*μ'` is
    the law of `(χ[u], χ[v])` under `μ'`. Hence
    `d(law(χ[00], χ[01]), law(χ[u], χ[v])) ≤ ε_g`.
  - In the same way, `d(ν_0, ν_u) ≤ ε_{g_u}`, `d(ν_0, ν_v) ≤ ε_{g_v}` and
    `d(ν_1, ν_0) ≤ ε_{h_3}`.
- *Convolution.*
  - Chaining with the definition of `α`:
    `d(law(χ[00], χ[01]), ν_0 ⊗ ν_0) ≤ ε_g + α + ε_{g_u} + ε_{g_v} ≤ ε' + α`.
  - `χ` is a homomorphism and `1_{[0]} = 1_{[00]} + 1_{[01]}`, so `χ[0] = χ[00] + χ[01]`, and
    `ν_0` is the push-forward of `law(χ[00], χ[01])` under addition. Therefore
    `d(ν_0, ν_0 * ν_0) ≤ ε' + α`.
- *Cases.* Put `κ = 2(ε' + α)`.
  - If `κ > 1/4` or `η' ≥ 1 − 4κ`, then `η' + 8ε' + 8α ≥ 1`, and the bound is trivial.
  - Otherwise Lemma 1 gives `ν_0({0}) ≥ 1 − 2κ`, and so `ν_1({0}) ≥ 1 − 2κ − ε'`. Since
    `χ[C] = χ[0] + χ[1]`,
    `μ'(χ[C] ≠ 0) ≤ 4κ + ε' ≤ 9ε' + 8α ≤ η' + 25ε' + 8α`. ∎

## 4. Proof of the theorem

Integrate Lemma 3 over `ρ`:
- `∫ η_y dρ = ∫ |e(χ[0]) − 1| dμ`;
- `∫ ε'_y dρ = Σ_k ∫ d(k_*μ_y, μ_y) dρ = Σ_k d(k_*μ, μ)`, by Lemma 2;
- `∫ α_y dρ = ᾱ`.

This gives the stated inequality, with constant `9` in place of `25` (the target states the
weaker `25`). ∎

## 5. Proof of the corollary

- *No central invariant vector.* The spectral projection `E({χ : χ[C] = 0})` is the projection
  onto `ker(π(1_C) − 1) = 0`. So `μ(χ[C] ≠ 0) = 1`.
- *Concentration.* By Cauchy–Schwarz,
  `∫ |e(χ[0]) − 1| dμ ≤ (∫ |e(χ[0]) − 1|² dμ)^{1/2} = ‖π(1_{[0]})ξ − ξ‖ ≤ ε`.
- *Moves.*
  - `⟨π(a)π(k)ξ, π(k)ξ⟩ = ⟨π(k^{-1}ak)ξ, ξ⟩ = ∫ (k·χ)(a) dμ`, possibly with `k^{-1}` in place
    of `k` depending on the product convention. This is harmless because `d` is symmetric
    and `‖π(k^{-1})ξ − ξ‖ = ‖π(k)ξ − ξ‖`. So `k_*μ` is the spectral law of `π(k)ξ`.
  - For any projection `P`: `|‖Pξ‖² − ‖Pξ'‖²| ≤ 2‖ξ − ξ'‖`. Hence
    `d(k_*μ, μ) ≤ 2‖π(k)ξ − ξ‖ ≤ 2|k|_S ε`.
- *Conclusion.* Substituting into the theorem gives `1 ≤ ε + 50Lε + 8ᾱ`. ∎

## 6. Remarks

- *Admissible pairs exist at every depth.* Take a finite partition of `C` into cones containing
  `[u]` and `[v]` (possible because `[u] ∪ [v] ≠ C`), and let `g` be a prefix-replacement map
  onto a partition containing `[00]` and `[01]`. The word length of such elements is bounded in
  terms of the number of carets. This is not used above, where `L` enters only through `|k|_S`.
- *Sanity checks.*
  - The Bernoulli cone products of `cantor-integer-maps-pair-lacks-relative-property-t-proof`
    are nearly independent across disjoint cones, and they satisfy the conclusion: they live on
    `χ[C] = 0`.
  - Positive-drift and extractable laws are killed elsewhere.
- *What survives.* The theorem uses only the identity `χ[0] = χ[00] + χ[01]` and approximate
  exchangeability of the two summands with an independent pair. A witness must therefore couple
  the phases of distant cones through something that is not a `V`-invariant function of `χ`.
  One example would be a random scale that `V` shifts, as in scale mixtures. For a scale-mixed
  Gaussian halving tree, however, the anisotropic depth shift of `h_1` already breaks joint
  almost invariance (not recorded as a theorem here).

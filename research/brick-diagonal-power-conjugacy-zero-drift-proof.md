---
rg: 2
id: brick-diagonal-power-conjugacy-zero-drift-proof
kind: route
title: Spread an invariant measure over the code pieces, compare drifts, and use boundedness of the drift set
target: brick-diagonal-power-conjugacy-forces-zero-drift
requires:
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
---

Let `𝒟 = { D_ν(b) : ν a b-invariant probability measure } ⊆ R^k`. It is nonempty (compactness) and
bounded by the table length `L(b)`, since `|δ_b| <= L(b)` pointwise. We use the cocycle rule
`δ_{fh}(x) = δ_f(hx) + δ_h(x)`, and `δ_{f^{-1}}(f x) = -δ_f(x)`.

**Step 1 (spread).** Let `ν` be `b`-invariant and put `ν' = (1/m) Σ_i (e_i)_* ν`. On `X_i`,
`b^m = δ_e(b) = e_i b e_i^{-1}`, and `(e_i)_* ν` is invariant under `e_i b e_i^{-1}`. So `ν'` is a
`b^m`-invariant probability measure.

**Step 2 (drift is preserved).** For `y` in the support of `(e_i)_*ν`, write `y = e_i x`. Then
`δ_{b^m}(e_i x) = δ_{e_i b e_i^{-1}}(e_i x) = δ_{e_i}(b x) + δ_b(x) - δ_{e_i}(x)`.
Integrate against `ν`. The two `δ_{e_i}` terms cancel by `b`-invariance of `ν`, and `δ_{e_i}` is
bounded. So `∫ δ_{b^m} dν' = (1/m) Σ_i ∫ δ_b dν = D_ν(b)`.

**Step 3 (average back).** Put `ν'' = (1/m) Σ_{j<m} b^j_* ν'`, which is `b`-invariant. By the cocycle
rule, `δ_{b^m} = Σ_{j<m} δ_b ∘ b^j`, so
`∫ δ_{b^m} dν' = Σ_{j<m} ∫ δ_b d(b^j_* ν') = m ∫ δ_b dν'' = m D_{ν''}(b)`.

**Step 4.** By Steps 2–3, every `D ∈ 𝒟` equals `m D'` for some `D' ∈ 𝒟`. Iterating, `D = m^j D_j`
with `D_j ∈ 𝒟`, so `|D| <= L(b)/m^j` for all `j`. Hence `D = 0`.

**Corollaries.**
- **Pointwise.** If coordinate `ℓ` of `δ_b` is everywhere `>= 1` (or everywhere `<= -1`), then
  `D_ν(b)_ℓ ≠ 0` for every invariant `ν`, contradicting the theorem.
- **Extra coordinates.** A `(b × id)`-invariant measure on `C^{k+l}` projects to a `b`-invariant
  measure on `C^k`. The first `k` drift coordinates agree, and the rest vanish.
- **Recovering item 3(b).** Odometers satisfy `δ_e(T) = T^m` by item 3(c) of
  `renormalizable-thompson-elements-are-odometer-codes`. ∎

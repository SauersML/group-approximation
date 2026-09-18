---
rg: 2
id: thompson-f-dyadic-ea-witnesses-need-tower-size-proof
kind: route
title: Thicken each set into a box of lamp configurations, push along the free breakpoint-cocycle action to F, and apply Moore's tower bound
target: thompson-f-dyadic-ea-witnesses-need-tower-size
requires: [thompson-f-folner-function-exceeds-every-tower, thompson-f-amenable-iff-dyadic-action-extensively-amenable]
---

Notation as in the claim, plus Steps 1 and 5 of `thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof`:

- `c_g = β(g⁻¹)`;
- the affine action `g ∗ φ = c_g + g·φ` of `F` on `Z^{(D)}`, which is free.

Moore's Følner condition, from `thompson-f-folner-function-exceeds-every-tower` (arXiv:0905.1118v7, §2),
reads verbatim: "A finite subset $A$ … is $\varepsilon$-Følner … if $\sum_{\gamma \in \Gamma} |(A \cdot
\gamma) \symdif A| < \varepsilon |A|$".

## Step 1. Boxes

Fix an integer `N ≥ 1`. For finite `S ⊂ D` let `Box(S) = {φ ∈ Z^{(D)} : supp φ ⊆ S, |φ(x)| ≤ N}`, of size
`(2N+1)^{|S|}`, and let `U_S` be the uniform probability measure on it. Put `ν' = Σ_S ν(S) U_S`. This is a
probability measure on `Z^{(D)}` with `|supp ν'| ≤ |supp ν|·(2N+1)^k`.

## Step 2. One box moved by a generator

Let `s ∈ Γ`. The map `φ ↦ s ∗ φ` sends `U_S` to the uniform measure on `c_s + Box(sS)`.

Since `c_s = β(s⁻¹) = −s·β(s)` (from `β(s⁻¹s) = 0` and (R)), `supp c_s = s(B(s))`.

- If `B(s) ⊆ S`, then `supp c_s ⊆ sS`, and `c_s + Box(sS)` is a translate of the product box `Box(sS)`
  inside the coordinates `sS`. For a product of intervals of length `2N+1`, translating by `v` changes the
  uniform measure by at most `Σ_x 2|v(x)|/(2N+1)` in `ℓ¹`. So `‖s ∗ U_S − U_{sS}‖₁ ≤ 2‖c_s‖₁/(2N+1)`, and
  `‖c_s‖₁ = ‖β(s)‖₁`.
- Otherwise, the trivial bound is `‖s ∗ U_S − U_{sS}‖₁ ≤ 2`.

## Step 3. Invariance of ν'

`Σ_S ν(S) U_{sS} = Σ_T (sν)(T) U_T`. Hence

`‖s ∗ ν' − ν'‖₁ ≤ Σ_S ν(S) ‖s ∗ U_S − U_{sS}‖₁ + ‖Σ_T ((sν)(T) − ν(T)) U_T‖₁`
`            ≤ 2‖β(s)‖₁/(2N+1) + 2 Σ_{y∈B(s)} ν{S : y ∉ S} + ‖sν − ν‖₁`.

Summing over `Γ`: `Σ_{s∈Γ} ‖s ∗ ν' − ν'‖₁ ≤ δ := ε₁ + 2ε₂ + 2L/(2N+1)`.

## Step 4. Push to F

The action `∗` is free, so choosing one base point `φ_O` in each orbit `O` defines `π : Z^{(D)} → F`,
`π(g ∗ φ_O) = g`. Freeness makes it well defined, and `π(h ∗ φ) = hπ(φ)`. Let `μ = π_*ν'`, a probability
measure on `F` with `|supp μ| ≤ |supp ν'|`.

Pushforward along an equivariant map does not increase `ℓ¹` distance, and `π_*(s ∗ ν') = s·μ` with
`(s·μ)(x) = μ(s⁻¹x)`. So `Σ_s ‖sμ − μ‖₁ ≤ δ`.

## Step 5. Level sets (Namioka)

For `t ≥ 0` let `A_t = {x : μ(x) > t}`, so `A_t ⊆ supp μ` and `{sμ > t} = sA_t`. Layer-cake gives
`‖sμ − μ‖₁ = ∫₀^∞ |sA_t Δ A_t| dt` and `1 = ∫₀^∞ |A_t| dt`.

Suppose `δ < C^{−n}`. If every nonempty `A_t` had `Σ_s |sA_t Δ A_t| ≥ C^{−n}|A_t|`, integrating would give
`δ ≥ C^{−n}`. So some nonempty `A = A_t` has `Σ_{s∈Γ} |sA Δ A| < C^{−n}|A|`.

Put `A' = A⁻¹`. Then `A'γ = (γ⁻¹A)⁻¹`, so `|A'γ Δ A'| = |γ⁻¹A Δ A|`. Since `Γ` is symmetric,
`Σ_γ |A'γ Δ A'| < C^{−n}|A'|`, i.e. `A'` is `C^{−n}`-Følner in Moore's sense. By Moore's Theorem 1.1,
`exp_n(0) ≤ |A'| = |A| ≤ |supp μ| ≤ |supp ν|·(2N+1)^k`.

## Step 6. Choice of N

Assume `ε₁ + 2ε₂ < C^{−n}/2`, and take `N = ⌈2LC^n⌉`. If `L = 0` then `Γ ⊆ {1}` does not generate `F`,
so `L ≥ 1`.

- `2N+1 > 4LC^n`, so `2L/(2N+1) < C^{−n}/2` and `δ < C^{−n}`.
- `2N+1 ≤ 4LC^n + 3`.

Step 5 gives `|supp ν|·(4LC^n + 3)^k ≥ exp_n(0)`.

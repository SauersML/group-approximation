---
rg: 2
id: laurent-extension-agrees-iff-inverse-defects-commute
kind: claim
title: A unit-type vertex rounding extends to the Laurent Steinberg group exactly when d inverse-root defects commute with the rounding
distinct_from:
  laurent-vertex-rounds-for-every-model: that is the open rounding claim for the Laurent vertex; this is an established criterion that reduces it, for a given unit-type rounding, to d commutation conditions in the ultraproduct.
  theorem-e-vertex-rounds-to-unit-type-representations: that asks for a unit-type rounding of the polynomial vertex; this assumes one and decides when its canonical Laurent extension still rounds.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**ESTABLISHED.** Let `R_+ = F_q[x_1..x_d] ⊂ L = F_q[x^(±1)]`, `Γ = EL_r(R_+) < Δ = EL_r(L)`, with `r, d >= 3`.
Let `q : St_r(L) -> Δ` be the quotient and `M = prod_U M_n`.

Let `σ : Δ -> U(M)` be a homomorphism, and `π_n : Γ -> U(n')` genuine representations with `π = σ` on `Γ` in `M`.
Assume each `π_n` factors through `St_r(A_n)` for a finite ring `A_n`, a quotient of `R_+` in which every `x_i` is
a unit. Let `ρ'_n : St_r(L) -> U(n')` be the canonical extension along `L -> A_n`, and `ρ' = (ρ'_n)_U`. Define the
inverse-root defects

```text
W_i = ρ'(x_23(x_i^(-1)))^* · σ(e_23(x_i^(-1)))  ∈ U(M),     i = 1..d.
```

1. **Partial commutation, unconditional.** `W_i` commutes with `π(H_i)` for a subgroup `H_i ⊂ Γ` that contains
   every `e_jk(x_i^2 R_+)`. At every finite level `π_n(H_i) = π_n(Γ)`.
2. **Criterion.** `σ∘q = ρ'` on `St_r(L)` in `M` if and only if every `W_i` lies in `π(Γ)' ∩ M`.
3. **The gap is ultraproduct non-rigidity of `H_i`.**
   - `π(H_i)' ∩ M` and `π(Γ)' ∩ M` can differ even though `π_n(H_i) = π_n(Γ)` for every `n`.
   - The inverse of `x_i` in `A_n` is `x_i^(m_n - 1)`, where `m_n` is the multiplicative order of `x_i` in `A_n`.
   - If `σ` is trace-preserving, then `m_n -> ∞` along `U`. Otherwise some fixed `x_i^m - 1` dies in every `A_n`,
     and `σ(e_12(x_i^m - 1)) = 1`, which contradicts the regular trace.
   - So `π_n(e_12(1)) = π_n(e_12(x_i^2 u_n))`, where `u_n ∈ R_+` has unbounded degree. Commuting with each fixed
     element of `H_i` gives no control on it.
4. **Consequence for the Laurent claim.** For a trace-preserving model, `σ|Δ` rounds on `St_r(L)` to `ρ'` exactly
   when some unit-type rounding of `σ|Γ` has commuting defects.
   - Conversely, a Laurent rounding `ρ_n` makes `ρ_n|Γ` such a rounding, with every `W_i = 1`.
   - The descent from `St_r(L)` to `Δ` is not decided here. `ρ'` kills `K_2(r, L)` in `M`, but at finite level
     `ρ'_n` need not. The symbols `{x_i, x_j}` can have unbounded `p`-power order in `K_2(A_n)`.

Proof: `laurent-extension-agrees-iff-inverse-defects-commute-proof`.

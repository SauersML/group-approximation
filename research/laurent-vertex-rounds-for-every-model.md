---
rg: 2
id: laurent-vertex-rounds-for-every-model
kind: claim
title: Every trace-preserving representation of the Theorem E actor rounds on the Laurent vertex EL_r(F_q[x^±1]) to genuine representations
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1), rounding on the polynomial vertex EL_r(F_q[x_1..x_d]); this rounds on the larger Laurent vertex EL_r(F_q[x^±1]), whose genuine representations restrict to unit type with no rate.
  theorem-e-vertex-rounds-to-unit-type-representations: that is unit-type rounding of the polynomial vertex; this is a rounding statement for a different Kazhdan subgroup that implies it exactly, with P_n = 1.
  kt-wreath-relative-canonical-actor-exactification: that rounds the whole actor, including SL_d(Z), on canonical wreath microstates; this rounds only the normal Laurent vertex, for every trace-preserving model.
  vertex-rounding-with-log-depth-rate: that is polynomial-vertex rounding with a quantitative defect condition; this is Laurent-vertex rounding, which needs no rate.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**OPEN.** Let `Δ = EL_r(F_q[x_1^(±1)..x_d^(±1)]) < G = Δ ⋊ SL_d(Z)`, with `r, d >= 3`, and fix a finite
generating set `F_Δ`. For every trace-preserving `σ : G -> U(prod_U M_n)`, after `o(n)` padding there should be
genuine representations `ρ_n : Δ -> U(n')`, with `n'/n -> 1`, such that

```text
max_(s ∈ F_Δ) ||σ_n(s) - ρ_n(s)||_2  ->  0     along U.
```

**Payoff.** Restricting `ρ_n` to `Γ = EL_r(F_q[x_1..x_d])` gives a unit-type rounding with `P_n = 1` exactly
(route `unit-type-rounding-via-laurent-vertex-rounding`). No compressor transport, torus bound or rate is needed.

## Attempts

- **Strict stability.** Impossible. `Δ` is infinite, residually finite and Kazhdan (Ershov–Jaikin-Zapirain),
  so Becker–Lubotzky (arXiv:1809.00632, abstract) applies. This claim is flexible, and flexible HS stability of
  higher-rank Kazhdan groups is open.
- **Robust spectral gap.** Insufficient, for the same reason as for `Γ` in
  `hs-stable-vertex-rounding-for-every-model`: `(T;FD)_rob` supplies no genuine representation.
- **Deduce it from polynomial-vertex rounding.** Reduced to `d` commutation conditions. Not closed.
  - The opposite implication holds. By `log-depth-rate-rounding-via-laurent-vertex-rounding`, this claim implies
    `vertex-rounding-with-log-depth-rate`, so it is at least as strong as input 1.
  - A unit-type rounding of `Γ` extends along `L -> A_u` only to `St_r(L)`.
  - By `laurent-extension-agrees-iff-inverse-defects-commute`, that extension agrees with `σ` on `St_r(L)` exactly
    when the `d` defects `W_i = ρ'(x_23(x_i^(-1)))^* σ(e_23(x_i^(-1)))` commute with `π(Γ)`.
  - Each `W_i` commutes unconditionally with `π(H_i)`, and `π_n(H_i) = π_n(Γ)` at every finite level. The gap is
    rigidity of ultraproduct commutants.
  - Under a regular trace the inverse `x_i^(m_n - 1)` has unbounded degree, so commuting with each fixed element
    of `H_i` gives no control. This is the same high-degree mechanism the log-depth rate targets.
  - Descent from `St_r(L)` to `Δ` also stays open: the symbols `{x_i, x_j}` can have unbounded order in `K_2(A_n)`.
- **Restrict to wreath models.** It pays only through lamp covariance.
  - Regular trace and a trace-zero symmetry in the vertex commutant can be added to any model by tensoring with
    finite-quotient models and `1_2`, without changing the root spectra of a rounding.
  - See artifact §5.

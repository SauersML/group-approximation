---
rg: 2
id: shadow-avoidance-column-isometry-proof
kind: route
title: Compute the column isometry's shadow
target: shadow-avoidance-fails-at-column-isometries
requires: []
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

Direct computation.  `z*z = Σ_k e_{11} ⊗ u_k^* u_k / d = e₁₁ ⊗ 1`, so
`z` is a partial isometry with `‖z‖ = 1` and
`‖z‖₂² = τ(z*z) = tr_d(e₁₁) = 1/d`.  The conditional expectation onto
`M_d` is `id ⊗ τ'`, and `τ'(u_k) = 0` gives `E_{M_d}(z) = 0`, so `z`
is a legitimate residue of a packet 2-norm-approximated by `M_d`
(e.g. `y = d₁ + z` for any `d₁ ∈ M_d`).  For any nonzero projection
`s' ∈ R'`: `1⊗s'` commutes with `e₁₁⊗1`, so
`‖z(1⊗s')‖² = ‖(1⊗s')z*z(1⊗s')‖ = ‖e₁₁⊗s'‖ = 1`.

Quantifier check against the refuted claim: it demanded, for each
`ε > 0` and packet size `j`, a `δ₀(ε,j)` valid for EVERY
finite-dimensional subfactor and every `j` elements of 2-norm below
`δ₀`; here `j = 1`, the 2-norm `d^{-1/2}` drops below any `δ₀` for
large `d`, and both one-sided kill conditions fail at `ε` for every
`ε < 1` (the right-hand condition alone already fails).  Trace-zero
unitaries exist in `R' ≅ R` (Haar unitaries), so the family is
realized inside `R` for every `d`.

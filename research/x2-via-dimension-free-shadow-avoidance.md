---
rg: 2
id: x2-via-dimension-free-shadow-avoidance
kind: route
title: Dimension-free shadow avoidance closes Problem X(2) through local AFD
target: stw99-problem-x2-hyperfinite-factor-quasidiagonal
requires: [dimension-free-shadow-avoidance-in-hyperfinite-factor, popa-projection-formulations-of-x2]
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

**DEAD**: the first premise is refuted by
`shadow-avoidance-fails-at-column-isometries`; the implication below
remains valid and the route is kept as the record of it.

Given a finite packet `Y ⊂ R` and `ε`, hyperfiniteness supplies a
finite-dimensional subfactor `M_d` with residues
`z_i = y_i − E_{M}(y_i)` of 2-norm below `δ₀(ε, |Y|)` — no rate
needed, because the first premise is dimension-free.  The avoidance
projection `s' ∈ M_d' ∩ R` then yields `s = 1⊗s'` and `B = M_d ⊗ ℂs'`
satisfying Popa's local-AFD condition at `(Y, 2ε)` exactly as in
`x2-rate-controlled-local-afd-proof`.  The second premise converts
local AFD for all packets into quasidiagonality of `R`.

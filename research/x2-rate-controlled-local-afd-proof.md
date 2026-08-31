---
rg: 2
id: x2-rate-controlled-local-afd-proof
kind: route
title: Spectral cuts in the relative commutant prove the rate-controlled cell
target: x2-local-afd-holds-at-rate-controlled-packets
requires: []
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

Write `y_i = d_i + z_i` with `d_i ∈ M`, `‖z_i‖ ≤ 2`, `‖z_i‖₂ ≤ δ`
(after the harmless replacement of the best approximant).  Decompose
`z_i = Σ_{k,l} e_{kl} ⊗ z_i^{kl}` over `R = M_d ⊗ R'`; each corner has
`‖z_i^{kl}‖ ≤ ‖z_i‖` and, since `τ = tr_d ⊗ τ'` gives
`‖z‖₂² = d^{-1} Σ_{kl} ‖z^{kl}‖₂'²`, also `‖z_i^{kl}‖₂' ≤ √d·δ`.

**Spectral cut.**  For `η = ε/d` and each `(i,k,l)` let `q'` be the
spectral projection of `z_i^{kl*} z_i^{kl}` (and of
`z_i^{kl} z_i^{kl*}`, for the right-hand kills) for the interval
`(η², ∞)`; then `τ'(q') ≤ ‖z_i^{kl}‖₂'²/η² ≤ d·δ²/η²` and
`‖z_i^{kl}(1−q')‖ ≤ η` (compress: `(1−q')z^{*}z(1−q') ≤ η²`).

**Avoidance projection.**  `s' := 1 − ⋁ q'` over all `2jd²` cuts:
`τ'(1−s') ≤ 2jd² · dδ²/η² = 2jd⁵δ²/ε² ≤ 1/2 < 1` by the rate
hypothesis, so `s' ≠ 0`.  For every corner, `s' ≤ 1−q'` gives
`‖z_i^{kl} s'‖ ≤ η` and `‖s' z_i^{kl}‖ ≤ η`.  Assembling the matrix,
`‖z_i (1⊗s')‖ ≤ d·max_{kl}‖z_i^{kl}s'‖ ≤ d·η = ε`, likewise on the
left.

**Local AFD.**  Set `s := 1⊗s'` and `B := M ⊗ ℂs'` (unit `s`,
finite-dimensional, support `s`).  Then `[d_i, s] = 0`, so
`‖[y_i, s]‖ = ‖[z_i, s]‖ ≤ ‖z_i s‖ + ‖s z_i‖ < 2ε`.  And
`s y_i s = d_i s + s z_i s` with `d_i s ∈ B`, so, `E_B` being
contractive,
`‖s y_i s − E_B(s y_i s)‖ ≤ ‖s z_i s‖ + ‖E_B(s z_i s)‖ < 2ε`.

Model checks: (i) for `Y ⊂ M` (δ = 0) the statement collapses to
`s = 1`, `B = M`, both conditions exact — sanity; (ii) the fast-tail
element `y = Σ 8^{-n} u_n` at level `n` has `δ ≈ 8^{-n}`,
`d = 2^n`, and `2j·d⁵δ²/ε² = O(2^{-n})/ε² → 0` — the cell is
nonempty beyond finite-dimensional packets; (iii) the crude
`d·max` matrix bound is where the exponent `5/2` comes from; a
Hilbert--Schmidt-type bound would improve it to `3/2`, but no
bookkeeping removes the dimension dependence entirely — that residue
is `dimension-free-shadow-avoidance-in-hyperfinite-factor`.

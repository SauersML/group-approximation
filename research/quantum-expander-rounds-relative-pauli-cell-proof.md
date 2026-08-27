---
rg: 2
id: quantum-expander-rounds-relative-pauli-cell-proof
kind: route
title: Expect to the commutant, polar-round, then exactify one fixed D8 table
target: quantum-expander-rounds-relative-pauli-cell
requires:
  - quantum-expander-relative-commutant-rounding
---

Apply `(QEC1)` separately to `P` and `Q`. They are uniformly close to
`E(P),E(Q) in I_N tensor M_r`. Functional calculus inside that commutant
rounds the almost self-adjoint involutions to exact involutions without a
dimension factor. Fixed-word telescoping transfers the approximate
anticommutation relation to the rounded pair.

The remaining relations are the multiplication table of one fixed
extraspecial group `D_8`, not of the accumulated `N`-dimensional Clifford
packet. Apply finite-group Hilbert--Schmidt stability to this fixed table on
the residual factor `M_r`. Its correcting flexible isometry, tensored with
`I_N`, preserves the old spin factor. All losses depend only on `D`,
`lambda`, and the one-cell accuracy, proving uniformity in `N`.

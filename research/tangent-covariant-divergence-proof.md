---
rg: 2
id: tangent-covariant-divergence-proof
kind: route
title: Use endpoint oddness before applying the CP Green polynomial
target: tangent-commutator-covariance-bypasses-code-riesz-endpoint
requires:
  - complete-overlay-row-newton-is-a-code-riesz-multiplier
  - code-laplacian-has-uniform-cp-green-approximants
  - involution-augmented-code-jacobian-adds-no-cb-loss
---

For reflection tuples the displayed conjugation identity is exact.  Its
derivative at a commuting tuple proves endpoint oddness for the raw
commutator residual.  Left multiplication by `-S_iS_j/2` is the standard
unitary tangent trivialization (up to the harmless factor `1/2`) and
commutes with `Ad(S_j)`, proving `(TCB2)` for the `b_ij` used in `(CRM1)`.
Thus the support-coordinate Schur mask in `(CRM2)` is redundant on the
tangent commutator range.  Apply
the operator Cauchy--Schwarz/Jensen inequality to the normalized sum in
`(TCB3)` to obtain `(TCB4)` simultaneously for rows, columns, and matrix
amplifications.

Characterwise, tangentness forces the `j`-th perturbation block to vanish
unless the difference character has `j` in its support.  Summing `(CRM1)`
over all `j` therefore gives `(TCB5)` modulo the average over the support,
which is precisely the simultaneous-conjugation gauge.  The CP Green
identity `G_K Delta=I-A^K` and the code distance gap prove `(TCB6)`.

For `(TCB7)`, insert `X_j^2=I-E_j` into
`X_j(X_iX_j-X_jX_i)X_j+(X_iX_j-X_jX_i)` and cancel the exact-reflection
terms.  Contractivity of `X_i,X_j` gives the stated `L_2` bound.

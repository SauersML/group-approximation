---
rg: 2
id: tagged-a3-associator-positive-root-proof
kind: route
title: Compute both A3 bracketings and apply positive-root local finiteness
target: tagged-a3-associator-cell-has-finite-positive-root-model
requires:
  - finite-positive-root-fragments-have-marked-regular-models
  - binary-leavitt-tagged-shift-table-has-centralizer-collisions
---

Apply `[x_ab(r),x_bc(s)]=x_ac(rs)` first to the inner commutator in
`(DAC2)` and then to the outer commutator.  This gives `(DAC3)`.  Applying
the same relation first on positions `(1,2,3)` and then `(1,3,4)` gives
`(DAC4)`.

Expand the two products in `(DAC5)`.  Orthogonality gives
`A_iB_i=q`, `A_jB_i=0`, and both products with `D_(ij)` equal zero.  The
second equation is the last three zero terms alone.  Substitution into
`(DAC3)` proves `(DAC6)`.

All matrices used are strictly upper triangular root matrices on four
ordered positions.  The finite-positive-fragment theorem therefore applies
to every finite address menu, including literal reuse of the displayed
coefficients and the range-sum fold.  Since `q!=0`, root-coordinate
faithfulness makes `x_14(q)` nonidentity.  Its regular translation has trace
zero, proving `(DAC7)` and the scoped no-go.


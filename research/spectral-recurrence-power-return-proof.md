---
rg: 2
id: spectral-recurrence-power-return-proof
kind: route
title: Freeze one MF coordinate and choose its recurrent power afterwards
target: spectral-recurrence-power-return-non-mf-criterion
requires: [finite-spectrum-unitary-power-recurrence]
artifacts:
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
---

If `w` survives a faithful norm-corona model, pass to coordinates with
`||w(U_n)-I||>=beta`.  Choose `Q>=8*pi/beta`, then freeze one coordinate whose
root defect is below `beta/(2C)`.  Finite-spectrum recurrence at its dimension
selects `m>=2` with `||w(U_n)^m-I||<=beta/4`.  Unitary conjugacy keeps
`a_m(U_n)w(U_n)a_m(U_n)^-1` at distance at least `beta` from the identity, so
the two sides differ by at least `3 beta/4`, contradicting the UPR upper bound.

The exponent is chosen by the proof after the coordinate is fixed.  The group
does not read the matrix dimension; uniform authentication permits the
quantifier order.  The operator-norm lower bound and its contradiction with a
uniform root budget are formalized respectively as
`NoRenormalizationCapacity.recurrent_power_far_from_unitary_conjugate` and
`NoRenormalizationCapacity.no_model_of_recurrent_uniform_power_return`.
The full frozen-coordinate composition, including qualitative unitary
recurrence, is
`NoRenormalizationCapacity.no_model_of_uniform_power_return`.

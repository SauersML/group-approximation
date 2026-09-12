---
rg: 2
id: atlas-equal-block-biunitary-witness
kind: route
title: Leave the tensor-flip stratum through an equal-block operator biunitary
target: leavitt-steinberg-hs-unstable
requires:
  - atlas-true-criterion-baseline
---

Write a relative unitary for the two regular `A8` charts as a
`20160 x 20160` matrix of operators on an external multiplicity space.
Amplify the multiplicity and require all operator blocks to have the same
Hilbert--Schmidt norm, with the row and column orthogonality of a unitary.
The proposed positive interpretation was that an operator-valued Hadamard,
quantum-Latin, or magic-block realization of this flatness should leave the
sparse tensor-flip/cartesian stratum while retaining the `4564` control
relations, after which noncommuting block phases could cancel the `72`
cartesian escapees.

This route is invalidated by
`atlas-equal-block-flattening-is-commutant-gauge`.  After one fixed
`|A8|`-fold stabilization, **every** relative unitary has an equal-block
representative obtained by right multiplication with a unitary in the first
chart commutant.  The represented second chart, and hence every relator
defect, is unchanged.  At the tensor flip this flattening is already a magic
operator-block unitary with rank-one blocks, while the two charts still
commute completely and all escapee defects remain `sqrt(2)`.

Thus equal block norms, quantum-Latin incidence, and magic-block flatness are
not gauge-invariant evidence of leaving the dead stratum.  A viable positive
ansatz must additionally control a gauge-invariant quantity, for example a
fixed cross-chart commutator/holonomy or the defect of an actual cartesian
escapee.

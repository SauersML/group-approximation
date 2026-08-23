---
rg: 2
id: atlas-multiplicity-two-six-row-audit-proof
kind: route
title: Evaluate the six literal words in the repeated binary chart
target: atlas-multiplicity-two-escape-fails-five-saturated-rows
requires:
  - atlas-multiplicity-two-packet-collision-hub-escape
artifacts:
  - experiments/atlas_multiplicity_two_six_relator_audit.py
  - experiments/atlas-multiplicity-two-six-relator-audit.json
---

Decode each stored `4 by 4` binary chart matrix and tensor it with `I_2`.
For factor-two syllables conjugate by the exact inverse of the frame
`401004080301c030`; multiply row bits over `GF(2)`.  Gaussian elimination
computes `rank(value-I)`, and repeated multiplication computes the orders.
The resulting table is `(M2S1)`.

The ambient group generated inside `GL8(2)` is finite and contains the first
chart `A8`.  Its regular representation restricts to `[G:A8] Reg(A8)`, while
the second chart is conjugate by the regular unitary of the same frame.
A nonidentity group element has canonical trace zero, proving the stated
`sqrt(2)` defects after regularization.

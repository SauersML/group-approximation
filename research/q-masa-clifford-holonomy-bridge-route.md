---
rg: 2
id: q-masa-clifford-holonomy-bridge-route
kind: route
title: Promote the q-MASA endpoint through Clifford covariance and multiplicity holonomy
target: q-masa-to-fresh-packet-morita-bridge
requires:
  - full-q-masa-forgets-selectors-retains-branches
  - controlled-pauli-corner-has-clifford-groupification
  - clifford-groupified-control-is-forced-balanced
  - controlled-nested-reset-needs-clifford-holonomy
  - finite-schur-clifford-packet-flexible-hs-exactification
---

First identify each used control with one of the equal relative-Pauli child
halves; a general q-MASA character support cannot be Pauli-completed without
changing its trace. Replace each resulting controlled payload by its CZ/CNOT
semidirect stable letter. The arbitrary multiplicity involutions cancel from
the local Pauli conjugation calculations. Couple those involutions globally
by the two-cell supplied by
`controlled-nested-reset-needs-clifford-holonomy`; without it the regular
stationary flow is an exact countermodel.

Apply fixed finite-packet exactification and the existing shared-overlap
estimates at each of the constant number of cells. The holonomy density bound,
not the vertex/edge restriction table, supplies the strict comparison. The
resulting discrepancy and local payment inequalities are precisely the five
clauses of the target bridge.

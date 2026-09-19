---
rg: 2
id: reset-ray-hnn-stationarity-proof
kind: route
title: Compare the exact full and child totals on the one scalar reset ray
target: reset-ray-hnn-return-is-stationary
requires:
  - symmetrized-reset-collapses-schur-flow-to-one-ray
  - hnn-selector-chart-transport-preserves-mark-and-types
  - oriented-schur-child-branching-identity
---

Equation `(SRC7)` gives the two totals in `(RHS1)`; their difference is
`2K_1n`, the active rank-jump surplus.  The same theorem says every child type
has multiplicity `2n`.  Exact HNN conjugacy preserves the complete child type
vector, so at the next reset every child type still has multiplicity `2n`.
The uniqueness of the reset ray forces `(RHS2)`.  Substitution into the next
full-packet formula from `(SRC7)` proves the strict deficit.  No asymptotic or
rounding estimate is involved.


---
rg: 2
id: iwahori-stratum-reconciliation-from-central-rank-surgery
kind: route
title: Apply exact modular rank surgery separately at both supplied vertices
target: iwahori-torsion-multiplicity-stratum-reconciliation
requires:
  - modular-multiplicities-reconcile-at-quadratic-rank-cost
artifacts:
  - research/artifacts/modular-multiplicity-rank-reconciliation-2026-09-08.md
---

Apply the prerequisite to each vertex representation of `pi` and the
corresponding representation of the supplied compatible pair `sigma`.
The two constructions preserve each exact modular relation and produce
the generator multiplicities of `sigma` without changing `sigma`.
Their maximum normalized-rank and HS movement bounds are `3delta^2`
and `2sqrt(3)delta` respectively. Fixed-word telescoping bounds the
change of every Iwahori residual by `Cdelta`.

This proves the stated qualitative common-stratum assertion. The
additional small multiplicity-discrepancy hypothesis is automatic
from finite spectral separation. Neither a defect-controlled endpoint
nor a nonlinear Newton theorem is a conclusion of this route.

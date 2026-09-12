---
rg: 2
id: high-density-via-hyperoctahedral-reflection-corner
kind: route
title: Reduce the high-density groupifier to one balanced accepting-corner holonomy
target: canonical-high-density-local-sector-groupifier
requires:
  - hyperoctahedral-reflection-common-q-context-atlas
  - hyperoctahedral-reflection-q-overlap-groupifier
---

Choose `t` so that the common defect `1/(tD+1)` is below
`Delta/(1+Delta)`.  The established hyperoctahedral packet puts every local
predicate on the literal same accepting projection `q` and balances every
shared binary marginal.  The open overlap groupifier supplies the literal
cross-context equalities and exact marked model.  Apply
`common-meet-local-sectors-pay-one-deficit`.

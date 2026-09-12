---
rg: 2
id: nonhyperlinear-via-high-density-local-sectors
kind: route
title: Force a common finite game state by total canonical codimension
target: non-hyperlinear-group
requires:
  - high-density-local-sectors-force-one-bcs-gram
  - canonical-high-density-local-sector-groupifier
---

In every canonical matrix microstate, exactify the finite subgroups carrying
the projections `q_c`.  Their normalized ranks converge to the canonical
Plancherel masses, so `(CHD1)` gives the strict total-deficit hypothesis of
`high-density-local-sectors-force-one-bcs-gram`.  The group-word rows
`(CHD2)` make the remaining terms in `(HD4)` tend to zero, contradicting the
fixed finite-dimensional game gap.  Hence the marked exact group cannot
have canonical matrix microstates and is nonhyperlinear.

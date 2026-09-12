---
rg: 2
id: fano-incidence-recurrence-no-go-proof
kind: route
title: Combine regular stationary type flow with finite-depth bulk padding
target: fano-incidence-recurrence-needs-a-nonstationary-two-cell
requires:
  - fano-point-line-intertwiner-has-a-2-adic-defect
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

Apply the regular stationary-flow theorem to every finite packet chart and
restriction edge.  It gives an exact positive type flow containing every
selector character, so the ghost line orbit survives all edge equations.

For any additional fixed list of integral incidence checks, choose a bulk
multiplicity divisible by all of their finite Smith moduli.  The leftover
rank is bounded by a constant depending only on that list.  Exactify the
whole return on the bulk and place every failure on the leftover subspace.
Fixed-word telescoping bounds all normalized-HS defects by a constant times
the square root of leftover rank over total dimension, which tends to zero.

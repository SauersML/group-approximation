---
rg: 2
id: radical-collision-route
kind: route
title: Solve hyperlinear versus sofic by a radical collision
target: hyperlinear-nonsofic-group
requires: [radical-collision-criterion, sofic-radical-hyperlinear-survivor]
artifacts:
  - notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md
  - GroupApproximation/Sofic/HyperlinearResidualDetector.lean
---

Once one explicit sofic-radical element has a hyperlinear detector, pass to
the detecting range.  The established radical-collision criterion proves
that this range is hyperlinear and nonsofic.  This route is strictly weaker
than constructing a faithful hyperlinear representation of a known
nonsofic group.

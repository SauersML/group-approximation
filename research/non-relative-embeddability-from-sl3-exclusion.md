---
rg: 2
id: non-relative-embeddability-from-sl3-exclusion
kind: route
title: Non-hyperlinearity of the SL3 HNN group forbids relative embeddability of its lattice pair
target: arithmetic-pair-is-not-relatively-embeddable
requires:
  - sl3-hnn-admits-no-amalgamated-free-haar-unitary
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
  - relatively-embeddable-pair-makes-the-hnn-group-hyperlinear
---

Same argument as `non-relative-embeddability-from-sl2-exclusion` for the
pair `SL_3(Z) <= SL_3(Z[1/2])`: relative embeddability would make `G_3`
hyperlinear and hence supply the amalgamated-free Haar unitary that the
prerequisite forbids.  This route covers the `SL_3` half of the target.

---
rg: 2
id: non-relative-embeddability-from-sl2-exclusion
kind: route
title: Non-hyperlinearity of the SL2 HNN group forbids relative embeddability of its lattice pair
target: arithmetic-pair-is-not-relatively-embeddable
requires:
  - sl2-hnn-admits-no-amalgamated-free-haar-unitary
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
  - relatively-embeddable-pair-makes-the-hnn-group-hyperlinear
---

For the pair `SL_2(Z) <= SL_2(Z[1/2])`: if `L(C) subset L(A)` were `RE/N_1`
with `N_1` Connes embeddable, `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`
would make `G_2` hyperlinear, and
`hnn-hyperlinearity-is-amalgamated-free-haar-unitary` would then produce
the amalgamated-free Haar unitary that
`sl2-hnn-admits-no-amalgamated-free-haar-unitary` forbids.  This route
establishes the `SL_2` half of the target; the `SL_3` half is
`non-relative-embeddability-from-sl3-exclusion`, and the target asserts
both.

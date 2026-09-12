---
rg: 2
id: stw77-zero-counterexample-junk-corner-proof
kind: route
title: Take the contrapositive of proper-support local stability
target: stw77-zero-counterexamples-trap-nonproper-model-corners
requires:
  - stw77-proper-support-models-force-oinfty-stability
---

If the conclusion failed, then for every finite `F subset phi(A)` and every
`epsilon>0` there would be a unital finite-dimensional subalgebra `D subset B`
approximating `F` within `epsilon` whose minimal block projections are all
properly infinite in `B`.  These are exactly the hypotheses of
`stw77-proper-support-models-force-oinfty-stability`, applied to
`C=phi(A)`.  That theorem would make `phi` O-infinity-stable, contradicting
the assumed failure.  Hence one finite packet and one positive tolerance
uniformly force a nonproper minimal model support.

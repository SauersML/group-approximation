---
rg: 2
id: piece-overlap-right-is-exactly-dehn-swap-closure-proof
kind: route
title: Close the circle and read what it cost
target: piece-overlap-right-is-exactly-dehn-swap-closure
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerPieceOverlapProof.lean
  - GroupApproximation/Sofic/GreendlingerDehnSwap.lean
---

Machine-checked in both directions, under `hR` (relators cyclically reduced)
and `hmetric : MetricSmallCancellation R (1/6)`.

**Forward.**  `dehnSwapClosed_of_pieceOverlap` is the critical-pair analysis:
an arbitrary swap is decomposed into the finitely many ways two symmetrized
relators can overlap, and every case except the named one is discharged by the
piece bound.  The named one is the hypothesis.

**Backward.**  `pieceOverlapRight_of_dehnSwapClosed` is immediate: the
configuration is a particular swap, so swap closure covers it.  This direction
takes no hypothesis, which is what makes the equivalence a statement about the
forward direction's cost.

**The consequence.**  An equivalence between an assumption and its intended
consequence means the reduction moved no strength.  Recording it prevents the
common failure of counting the critical-pair analysis as progress toward
closing the rewriting lane; the analysis is real work and its output is a
better-scoped statement, but the obligation is the same size.

## Reading it against the neighbouring result

[[deep-two-factor-regime-is-empty]] is the shape a *successful* narrowing takes
in this lane: an emptiness theorem that concludes `False` and deletes
configurations outright.  The contrast is the useful part --- when a reduction
lands as an iff, nothing was deleted; when it lands as a vacuity proof,
something was.

## The one asymmetry

Free closure is strictly downstream: `dehnFreeClosed_of_pieceOverlap` exists,
`dehnFreeClosed_of_dehnSwapClosed` runs the same way, and no upgrade carries a
free reduction back into a swap.  So the circle closes at the swap half only,
and free closure is not an alternative entry point to the residual.

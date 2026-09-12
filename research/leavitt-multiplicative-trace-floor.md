---
rg: 2
id: leavitt-multiplicative-trace-floor
kind: claim
title: Dimension-free multiplicative Leavitt trace floor
distinct_from:
  outer-root-leavitt-table: That is the exact algebraic table retained by the outer roots; this is the finite-tracial matrix obstruction after four common-coordinate contractions have been decoded.
  finite-window-decoder: This is the completed terminal inequality; the other is the open reverse-decoding theorem needed to produce its inputs from group microstates.
artifacts:
  - GroupApproximation/Sofic/LeavittTraceFloor.lean
  - notes/TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md
---

For contractions `T_0,S_0,T_1,S_1` in any nonzero finite matrix algebra,

```text
max(||T_0 S_0-1||_2, ||T_1 S_1-1||_2, ||T_0 S_1||_2)
  >= 2-sqrt(3) > 1/4.
```

The bound is independent of matrix size.  On a corner of fixed trace
`alpha`, the corresponding ambient normalized-HS floor is
`sqrt(alpha)(2-sqrt(3))`.  Hence the terminal contradiction is complete once
the three products are decoded on one positive-density coordinate corner.

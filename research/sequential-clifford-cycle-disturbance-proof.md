---
rg: 2
id: sequential-clifford-cycle-disturbance-proof
kind: route
title: Pinch the cycle in an arbitrary order and count local minima
target: sequential-pinchings-have-sharp-linear-disturbance-loss
requires:
  - sparse-clifford-cycles-refute-average-commutator-rounding
---

Use `(X+QXQ)/2=0` when `Q` anticommutes with `X`, and equality to `X` when
they commute.  A cycle coordinate survives the prior pinching channels
exactly when it is earlier than both neighbors.  Those surviving vertices
are independent, hence at most half the cycle.  Under a random order the
survival probability is exactly one third.  Compare the resulting constant
disturbance with the established `8/L` complete-pair energy.

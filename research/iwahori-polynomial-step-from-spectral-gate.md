---
rg: 2
id: iwahori-polynomial-step-from-spectral-gate
kind: route
title: Apply finitely many Landweber terms and control the exact-chart remainder in mixed norms
target: iwahori-spectral-residual-gate-has-polynomial-step
requires:
  - modular-vertex-charts-have-uniform-schatten-control
artifacts:
  - research/artifacts/iwahori-mixed-surgery-and-polynomial-step-2026-09-08.md
---

The prerequisite supplies the exact admissible parameterization and the
mixed operator/HS second-derivative bound. Differentiating its finitely
many unitary slots also bounds the HS adjoint in operator norm, because
the admissible-space projections are contractive central averages and
anti-Hermitian projection.

For `A=I-C^(-2)L L*`, the supplied parameter has linear residual
`f+LK=A^T f`. Hilbert spectral calculus and the stated low-singular
mass bound make this at most `e/4`. The polynomial expression gives
`||K||_2<=(T/C)e` and
`||K||_op<=((2^T-1)/C)||f||_op`, without applying a spectral projection
in operator norm. Taylor's integral remainder is bounded by
`(C/2)||K||_op||K||_2<=e/4` under the stated operator-residual
threshold. Thus the exact-chart output has residual at most `e/2`.
The chart movement bound gives the displayed generator cost.

No hypothesis about arbitrary HS-near pairs, preliminary surgery,
iteration closure, or a globally available residual-canceling direction
is inferred from this calculation.

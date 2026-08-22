---
rg: 2
id: clifford-green-stationarity-proof
kind: route
title: Evaluate the square-commutator residual on anticommuting reflections
target: clifford-packets-are-stationary-for-intrinsic-green-step
requires:
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
  - regularized-anchor-square-function-has-dimension-free-cut
---

Anticommutation gives `(CGS1)` and
`||[Q_i,Q_j]||_2^2=||2Q_iQ_j||_2^2=4` for `i!=j`.  Scalars are fixed by
every ucp pinching in `(IFG2)`, so `(IFG3)` is zero and `(CGS2)--(CGS3)`
follow.  Central direct sums scale every normalized squared
Hilbert--Schmidt quantity by the summand trace.  Finally the anchor odd part
of an anticommuting reflection equals the reflection itself, proving
`(CGS4)`.

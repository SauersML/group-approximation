---
rg: 2
id: low-odd-square-green-signal-proof
kind: route
title: Evaluate the skew square-commutator residual by Laurent calculus
target: low-odd-square-removes-pairwise-green-stationarity
requires:
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
  - regularized-anchor-cut-makes-residual-spikes-boundary-heavy
---

On a spectral value `U=e^(it)`, `(LOS1)` gives

```text
 R=sin^2(t),             omega=-i sin(t)cos(t).
```

This proves `(LOS2)` by functional calculus.  If `0<=R<=sI`, then
`R(I-R)>=(1-s)R`, proving `(LOS3)`.  Finally
`tau(R)=||[A,B]||_2^2/4` is the standard odd-square identity.

---
rg: 2
id: stinespring-and-phase-rounding-repair-cp-reflections
kind: route
title: Repair the CP reflection to an inner automorphism and round its implementing unitary to an involution
target: cp-reflection-near-idempotents-round-to-pinchings
requires: []
artifacts:
  - research/artifacts/cp-reflection-near-idempotent-pinching-2026-09-08.md
---

The CP reflection `Q=2P-id` is self-adjoint, bistochastic, and UCP,
with `||Q^2-id||_(infinity->2)=epsilon=4delta`. Consequently
`tau(1-Q(u)*Q(u))<=epsilon` for every source unitary `u`.

In a finite Stinespring dilation of `Q`, use `Tr/d`, normalizing the
rank-`d` encoding projection. Average that projection over the full
source unitary group and round the average spectrally. The repaired
projection commutes with the represented `M_d`, has rank a multiple
of `d`, and differs in normalized rank from one by at most `2epsilon`.
For `epsilon<1/2`, it therefore has rank exactly `d`. Principal-angle
alignment gives an inner automorphism `alpha=Ad(U)` with

```text
||Q-alpha||_(infinity->2)<=(4+2sqrt(2))sqrt(epsilon).
```

Telescoping compositions bounds `||alpha^2-id||_(infinity->2)`.
Haar averaging then puts `U^2` close in normalized `L^2` to a scalar.
Rescale `U` by a scalar square root and round each eigenvalue to the
nearer of `+1,-1`. The resulting involution gives the target pinching
expectation, with distance at most `28sqrt(delta)` in the small
defect range. The trivial bound two handles the other range and gives
the stated `min{2,30sqrt(delta)}` bound, including zero defect.

For `lambda>1/2`, the CP decomposition
`P=lambda id+(1-lambda)R` makes the self-adjoint spectrum of `P`
lie in `[2lambda-1,1]`. Spectral calculus directly bounds `id-P`
by `(P-P^2)/(2lambda-1)` in the pointwise Hilbert norm, proving the
linear estimate on the whole operator unit ball. The artifact proves
all dilation, alignment, Haar, and scalar-rounding estimates inline.

---
rg: 2
id: relative-h2-kernel-insensitivity-and-log-density-proof
kind: route
title: Separate Kubota kernel blindness from fixed-cycle index density
target: relative-h2-does-not-supply-passive-hs-obstruction
requires:
  - passive-core-quotient-has-relative-rational-h2
---

Kubota's relative quasirepresentation datum depends only on the image of the
relative homomorphism and explicitly forgets its kernel.  For the surjection
`K -> G`, it therefore cannot express the required asymmetric datum of a
representation exact on `K` with only the quotient relators approximate.

For the other standard promotion, fix an integral cellular two-cycle `z`.
The trace-log representative of its determinant pairing is a fixed finite
sum.  If all involved relator values are operator-`epsilon` close to the
identity in dimension `d`, then

```text
|kappa|/d <= C_z epsilon
```

by the principal-logarithm estimate and the trace bound.  Hence that fixed
pairing has vanishing normalized density along every operator-small
sequence.  This proves only that the standard pairing supplies no positive
trace-density Hilbert--Schmidt wall.  It neither constructs a sublinear-rank
surgery nor excludes a different analytic obstruction.  The split central
extension route also remains conditional on an unproved finite-type or
residual-finiteness input.

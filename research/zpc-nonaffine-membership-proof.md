---
rg: 2
id: zpc-nonaffine-membership-proof
kind: route
title: Compute a one-coordinate Fourier violation on three signed pairs
target: zpc-does-not-force-affine-haar-membership-law
requires:
  - affine-haar-process-fourier-modulus-compiler
---

On the six-point action `(ZAH1)`, both generators are involutions and commute,
`J` has no fixed point, and `u` acts on each `J`-orbit as either `1` or `J`.
Thus every ZPC equation holds.  The always-accept verifier makes the strategy
perfect without adding a condition.

Exactly two points, namely the pair with first coordinate `1`, are fixed by
`u`.  Hence its membership bit is one with probability `2/6=1/3`, and the
Fourier character of that bit has expectation

```text
(2/3)(+1)+(1/3)(-1)=1/3.
```

The modulus criterion then excludes an affine-Haar membership law.


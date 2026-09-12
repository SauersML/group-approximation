---
rg: 2
id: steinberg-marginals-via-small-weighted-transform-closure
kind: route
title: Close the Steinberg marginal equations in a small packet of weighted transforms
target: steinberg-fox-recurrence-forces-zero-marginals
requires:
  - steinberg-fox-marginal-pushes-are-explicit
---

Choose a nonconstant weight in the `b` or `d` coordinate, close its orbit
under the rational push maps, and try to obtain a bounded-size Fourier,
Radon, or moment subsystem that forces `P=H=0` without recovering every
pointwise chord equation.

This route is invalidated by
`steinberg-nonconstant-weights-generate-full-projective-module`: the affine
translations and the `u` Möbius pullback generate the full rank-one
projective permutation module.  With the existing constant equation, any
nonconstant weight packet expands to all point masses and hence to the full
pointwise recurrence.

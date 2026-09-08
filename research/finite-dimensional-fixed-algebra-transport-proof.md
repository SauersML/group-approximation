---
rg: 2
id: finite-dimensional-fixed-algebra-transport-proof
kind: route
title: Correct finite-dimensional covariance before normalizing the moving component
target: finite-dimensional-kazhdan-fixed-algebra-transport
requires:
  - kazhdan-asymptotic-commutant-transport
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

Lift the finite-dimensional algebra to exact matrix algebras and correct
the finitely many generator covariances by polar decomposition of averaged
intertwiners. The corrected conjugations give a genuine representation of L
on each algebra image, even when its kernel varies with the coordinate.

For an element fixed by tLt^-1 subtract its projection to the L-fixed
subspace and normalize the nonzero remainder in Hilbert--Schmidt norm.
Exact covariance makes the normalized vectors asymptotically tLt^-1-fixed
without dividing any error by their original mass. The required transport
theorem makes them L-fixed asymptotically, contradicting the Kazhdan gap on
the orthogonal complement. Sections 1--2 contain all lifting and norm
estimates. This is a written proof, not a new Lean kernel check.

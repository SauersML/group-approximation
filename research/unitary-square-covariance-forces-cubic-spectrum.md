---
rg: 2
id: unitary-square-covariance-forces-cubic-spectrum
kind: claim
title: Square covariance below the fifth-root radius forces approximate cubic torsion
artifacts:
  - research/square-covariance-cubic-spectrum-proof.md
  - experiments/verify_cubic_spectral_basin.py
  - research/artifacts/non-mf-without-property-t.md
distinct_from:
  one-small-higman-generator-collapses-the-four-cycle: this is a two-unitary spectral theorem with a sharp radius for cubic torsion; the four-cycle claim uses all four Higman relations to deduce collapse to the identity.
  higman-four-cycle-intrinsic-mf-seed: this theorem requires a spectral radius bound on one unitary; the intrinsic seed has no such hypothesis and remains unresolved.
---

Fix \(1/3\le a<2/5\), and set

\[
c_a=2\sin(\pi a),\qquad
\delta_a=2\sin\left(\frac{\pi(2-5a)}{10}\right).
\]

For every dimension and every pair of unitaries \(U,V\), if

\[
\|U-I\|\le c_a,
\qquad \delta=\|VUV^*-U^2\|<\delta_a,
\]

then

\[
\|U^3-I\|\le6\arcsin(\delta/2).
\]

The strict limiting radius \(2\sin(2\pi/5)\) is sharp for this cubic
conclusion: the four nontrivial fifth roots and their doubling permutation
satisfy exact square covariance at that radius but do not satisfy \(U^3=I\).
No sharpness is asserted for the defect threshold or the error coefficient.

This is a dimension-independent operator-norm theorem using finite-dimensional
spectral theory. It neither assumes nor proves that the pair is close to an
exact representation, and does not establish a non-MF group by itself.

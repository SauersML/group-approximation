---
rg: 2
id: finite-support-coarea-and-polar-compression-proof
kind: route
title: Average nested finite supports and cut one common threshold on the intrinsic rank scale
target: uniform-finitary-support-makes-torsion-tracially-visible
requires:
  - finite-group-opnorm-support-profile
  - covariant-square-function-has-common-reducing-threshold
artifacts:
  - research/artifacts/jacobson-surviving-head-has-a-tracial-core-2026-09-08.md
---

Sections 1--4 of the artifact prove the assertion. Correct one
containing finite subgroup per coordinate, then average nested
active projections through a finite conjugacy window. The positive
cutoff has rank at most `C` times the mark rank and is identity
on the mark's nonidentity spectral subspace.

In the coarea identity, at most `2 rank(e)` units of squared
unitary-entry mass meet a nonzero eigenvalue. This yields
`integral ||[q_t,U]||_HS^2 dt <=2 rank(e)||[e,U]||_op`.
One threshold therefore almost reduces all inspected group
matrices in the Hilbert--Schmidt norm divided by the mark rank's
square root. The threshold contains the whole marked support.

Compress and use the singular value decomposition to replace each
compressed contraction by a unitary in the same corner. The
compression error and every fixed multiplication error tend to
zero in normalized Hilbert--Schmidt norm. The finite-order mark
needs no polar change. Original norm-null elements remain
Hilbert--Schmidt null, proving the claimed kernel inclusion.

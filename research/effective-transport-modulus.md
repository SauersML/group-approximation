---
rg: 2
id: effective-transport-modulus
kind: claim
title: Explicit numerical modulus for the literal operator-norm obstruction
root: true
distinct_from:
  uniform-finite-mf-obstruction: The established compactness theorem gives an unspecified finite test and positive threshold; this claim asks for a computed modulus on the displayed relators from the rational Kazhdan gap.
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

Compute an explicit positive defect threshold and error function, directly
from the rational property-`(T)` certificate and the forty-one displayed
relators, that force every finite-dimensional approximate model to send the
marked word close to the identity uniformly in the dimension.

## Attempts

- `literal-base-explicit-kazhdan-pair` supplies an explicit honest
  eight-word affine Kazhdan pair with
  `kappaB=1/(5*sqrt(3000)+2)`. This is substantially stronger than merely
  knowing qualitative property `(T)`.
- `p13-rotation-relator-defect-219` expands the checked short-word replay:
  rotation-relator defect `delta` makes every substituted P13 relator defect
  at most `219*delta`.
- These constants do not yet compose into the requested modulus.
  `literal-transport-gap-step-is-noneffective` locates the exact gate:
  `WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues`
  is an ultralimit contradiction with an unspecified `exists N`. The
  affine property-`(T)` bridge is exact and uses arbitrarily long
  translation conjugators, so naive relator telescoping is not uniform.
- The smallest sufficient new input is a finite rational sum-of-squares
  certificate for the full affine base, or an explicit robust
  relative-property-`(T)` theorem for the affine relations. A later finite
  ledger must then cover compressor transport, spectral-corner restriction,
  and the marked-word estimate.
- Source drift: `non_mf_groups_exist.tex` is now the Leavitt manuscript and
  no longer displays the former forty-one-relator presentation. The legacy
  literal Lean modules and research nodes remain, but the artifact pointer
  above must be restored or replaced before a literal manuscript-level
  modulus can be advertised.

**OPEN.** No positive numerical relator threshold is justified by the current
proof declarations.

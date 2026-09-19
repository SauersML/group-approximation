---
rg: 2
id: nekrashevych-violation-recurrence-via-partial-center-return
kind: route
title: Use the balanced reset ray and partial-center Thompson return
target: nekrashevych-violation-density-recurrence
requires:
  - translation-symmetrized-full-schur-reset
  - symmetrized-reset-collapses-schur-flow-to-one-ray
  - oriented-schur-child-branching-identity
  - hnn-selector-chart-transport-preserves-mark-and-types
  - thompson-pauli-prefix-rounding-has-polynomial-cost
  - partial-center-thompson-schur-return
  - schur-violation-density-gives-contraction
---

Orient each fixed packet predicate toward violation.  The full reset forces
the complete selector/branch type vector onto its one scalar ray, so a fixed
positive fraction `beta` of every nonzero carrier lies in the violating
selector sectors (for a nonconstant predicate).  The child identity gives
`c_n=a_n+v_n` exactly on the corrected packet.  The partial-center return
turns that child vector into the next input vector while charging at most
`C(n+1)^k sqrt(E)` and, crucially, renews rather than centralizes the selector
chart.  These are `(SVG1)--(SVG3)` and `(NVR1)`.  Apply
`schur-violation-density-gives-contraction` to obtain the required strict
backward recurrence.


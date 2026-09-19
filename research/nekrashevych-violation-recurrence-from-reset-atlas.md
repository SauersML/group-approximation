---
rg: 2
id: nekrashevych-violation-recurrence-from-reset-atlas
kind: route
title: Return the corrected child chart without absorbing its branch flip into the spin prefix
target: nekrashevych-violation-density-recurrence
requires:
  - reset-schur-bcs-branching-atlas
  - non-ce-bcs-has-robust-approximate-energy-gap
  - oriented-schur-child-branching-identity
  - schur-violation-density-gives-contraction
  - branch-flip-pauli-extraction-cancels-schur-surplus
---

Use the branch flip only inside the finite reset which balances and names the
complete corrected child type vector.  Return the restriction to the child
chart itself through the recurrent atlas; do not include the flip in the
returned matrix factor.  Then `(RSA1)--(RSA3)` are exactly
`(SVG1)--(SVG3)`, and the robust non-CE BCS gap supplies the fixed `beta`.
The contraction lemma yields the target recurrence.  The cancellation theorem
is included as a guard: any implementation which turns the flip into the next
Pauli spin is rejected before the scalar inequality is invoked.


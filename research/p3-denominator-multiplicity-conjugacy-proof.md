---
rg: 2
id: p3-denominator-multiplicity-conjugacy-proof
kind: route
title: Apply the full-matrix commutant theorem and close only the Folner boundary
target: denominator-transport-only-conjugates-p3-multiplicity-reservoirs
requires:
  - finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge
  - regular-p3-parahoric-bands-have-twisted-gauge-surplus
  - folner-multiplicity-atlases-have-vanishing-first-exit
---

Multiply the supported denominator transition by the inverse of its fixed
packet intertwiner.  The result centralizes the full packet matrix algebra,
so it is exactly an arbitrary multiplicity unitary, proving `(DTR2)` and
`(DTR3)`.  Gauge those unitaries recursively along a depth tree.  On a finite
coweight box use the established inverse groupoid gauge for its native loops
and the regular-band gauge surplus at every object.  Complete only the
boundary shifts.  A radius-`R` word can fail on at most the `R`-boundary;
the universal bound `||U-V||^2<=4` per unit mass gives `(DTR4)`.

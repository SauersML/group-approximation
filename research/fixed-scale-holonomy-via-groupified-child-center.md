---
rg: 2
id: fixed-scale-holonomy-via-groupified-child-center
kind: route
title: Return violation-oriented Schur children through a groupified center chart
target: fixed-scale-contextual-multiplicity-holonomy
requires:
  - groupify-schur-child-center-chart
  - reset-schur-bcs-branching-atlas
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - oriented-schur-child-branching-identity
  - hnn-selector-chart-transport-preserves-mark-and-types
  - context-local-schur-packet-marked-extension
  - schur-violation-density-gives-contraction
  - bounded-overlap-syndrome-energy-accounting
---

Use the groupified corrected center, not the raw last Clifford generator, to
read the complete `Q`-child type vector. Its transverse reset removes the old
selector chart, and the HNN edge aligns the reset chart with the next context.
The recurrent atlas supplies `(RSA1)--(RSA3)` with bounded overlap.

The exact child identity gives child mass `a_n+v_n`, while the robust BCS gap
gives `v_n>=beta a_n-error`. Apply
`schur-violation-density-gives-contraction` and the contractive ladder. Exact
marked extension and groupified-chart completeness preserve positive base
carrier mass, producing the fixed-scale holonomy required by the target.

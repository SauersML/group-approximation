---
rg: 2
id: selector-product-payload-square-proof
kind: route
title: Multiply the two selector involutions and compress their commutator to the chosen atom
target: selector-product-is-a-payload-corner-square-root
requires:
  - one-bit-clifford-selector-halves-a-chosen-bcs-atom
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
  - binary-schur-canonical-weights-have-half-reservoir-escape
  - projective-gauge-charge-forces-morita-or-corner
---

For involutions, `(p_aq_a)^2=[p_a,q_a]`.  Multiply the right side of the
selector relation by `h_(a,v)=x_vJ^(a(v))`; centrality and involutivity give
`r_ah_(a,v)=J`.  On the assignment Reynolds atom `h_(a,v)=1`, yielding the
corner square.  The Pauli selector construction proves exact completeness.
For the boundary, tensor it with the established stationary equal-child
Schur model; without a cross-incidence row all local equations remain exact
and the branch payment is zero.

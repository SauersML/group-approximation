---
rg: 2
id: transport-kl-gate-through-left-comb-prefix-equivalence
kind: route
title: Apply the prefix elementary-root formula to the two far KL roots
target: canonical-left-comb-kl-gate-is-a-mixed-involution
requires:
  - leavitt-length-six-three-gate-weight-survivor
  - inverse-packet-conjugator-must-mix-s-and-t-charts
artifacts:
  - GroupApproximation/Leavitt/PrefixCode.lean
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
---

`prefixUnitsEquiv_elementaryUnit_val` sends `x_ij(a)` to
`1+s_(alpha_i)a t_(alpha_j)`.  Apply it to both factors of `q`.  Their row
and column indices are disjoint, so the two nilpotent parts annihilate in
both orders; characteristic two then gives the involution identity.


---
rg: 2
id: target-saturated-reynolds-return-firewall-proof
kind: route
title: Compute both directed Reynolds overlaps in the rectangular Leavitt packet
target: target-saturated-reynolds-return-does-not-lock-leavitt-reservoir
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - weyl-commutant-superrank-detects-rectangular-return
---

In the exact rectangular model, the source packet algebra is
`M_p tensor I_(pk)` and the target packet algebra is
`M_(p^2) tensor I_k`.  Their commutants are nested in the reverse order, so
the target Reynolds projection is a subprojection of the source Reynolds
projection.  The superrank formulas give traces `p^(-2)` and `p^(-4)`.

For an arbitrary returned copy, projection monotonicity bounds the overlap
by the target trace `p^(-4)`.  For the identity return the nesting makes this
an equality.  Subtracting from the source trace leaves the fixed complement
`p^(-2)-p^(-4)`.  Hence full target overlap occurs in the countermodel,
whereas source overlap would contradict rank.  This proves `(TSR1)--(TSR8)`.

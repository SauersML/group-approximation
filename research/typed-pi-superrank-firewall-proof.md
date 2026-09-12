---
rg: 2
id: typed-pi-superrank-firewall-proof
kind: route
title: Combine the Morita rectangular packet with the finite trace obstruction
target: typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - mixed-steinberg-loops-admit-morita-rectangular-model
  - weyl-commutant-superrank-detects-rectangular-return
---

Use the source/target Weyl model `(FWC2)--(FWC3)` on
`C^p tensor C^p`.  On its fixed nontrivial central phase the marked root is
`zeta I`, the source packet generates `M_p tensor I_p`, and the two-child
packet generates `M_(p^2)`.  Thus all separate PI assertions are their
literal matrix-algebra PI assertions, including `(FWC4)`, while `(WCS3)`
gives the two Reynolds ranks `(TPS1)`.

Interpret the branch coefficients as the two inclusions
`E -> E direct_sum E` and the two coordinate projections.  The block
transvection construction `(MSM1)--(MSM3)` realizes every typed
Steinberg multiplication triangle and every associativity refinement
exactly.  It does not identify `1_E` with `1_(E direct_sum E)`.

Finally apply the cyclic trace calculation in `(TPS3)` to the prescribed
root carrier `P=I`.  It rules out the three common-carrier Leavitt products
with residual below `1/3`, despite all of the preceding typed
finite-coordinate data being exact.


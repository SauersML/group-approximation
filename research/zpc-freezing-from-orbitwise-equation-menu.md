---
rg: 2
id: zpc-freezing-from-orbitwise-equation-menu
kind: route
title: Generate the frozen quotient representation from one orbitwise coherent menu fibre
target: zpc-readable-control-freezing-to-lcs
requires:
  - perfect-zpc-irs-quantum-gap-game
  - zpc-readable-variables-global-boolean-field
  - zpc-frozen-equation-menu-has-positive-orbitwise-class
  - orbitwise-scalar-relators-give-quotient-representation
---

Choose `r` and `P` from the orbitwise-menu claim.  Same-question and
edge-ZPC commutators hold globally, while `(ZOM2)` supplies every conjugate
of every frozen affine relator on `P`.  Apply
`orbitwise-scalar-relators-give-quotient-representation` to the unreadable
free group and the central involution `J`.  The resulting cyclic-hull
representation satisfies the frozen linear equations and prescribed
commutations, and it has `J=-I`.

Hence the frozen linear-commutation system has a nonzero operator solution
in its negative central sector.  By
`finite-linear-commutation-system-to-lcs`, the ordinary LCS `L(G,r)` has a
perfect commuting-operator strategy, proving readable-control freezing.

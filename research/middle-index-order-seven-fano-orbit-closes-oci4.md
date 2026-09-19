---
rg: 2
id: middle-index-order-seven-fano-orbit-closes-oci4
kind: route
title: Use the marked middle-index order-seven Fano orbit as the finite-coordinate OCI4 cut
target: finite-coordinate-el20-active-cut-inherits-order-seven-anchor
requires:
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Close the three-pair marked middle-index packet under the two order-seven
words `T_1=J_1B_2A_1` and `T_2=J_2B_3A_2`.  Select the constant character
atom in the resulting Fano orbits, and then close it under the remaining
center-chain arms.  The hoped-for conclusion is that orbit balance gives a
positive common reducing cut on which the two order-seven anchors identify
the native transports with the quarter/eighth center-chain Hecke maps.

This route is refuted by
`middle-index-order-seven-orbit-cut-is-native-scale-neutral`: the closure
does give a positive constant atom, but both Hecke heads have full source and
range on that atom, and an exact finite packet model makes it orthogonal to
the signed Hecke source.

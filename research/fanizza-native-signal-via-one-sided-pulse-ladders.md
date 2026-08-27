---
rg: 2
id: fanizza-native-signal-via-one-sided-pulse-ladders
kind: route
title: Decode the native Fanizza signal with affine returns and one-sided pulse ladders
target: fanizza-native-signal-groupification
requires:
  - fanizza-one-sided-pulse-ladders-give-computable-decoder
  - fanizza-et-al-computable-bcs-signal-family
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
---

Apply the pulse-ladder compiler to the finite instance `B_m`, retaining its
distinguished generator `d_m`.  Clause 1 of the compiler is exactly
`(NSG1)--(NSG2)`, with computable instance-dependent moduli.  If `m` halts,
the Fanizza membership GNS representation is perfect and has
`D_m=(1-d_m)/2` nonzero.  Clause 2 extends it to the compiled group without
changing `d_m`, so `d_m` is nonidentity in one exact representation.  These
are precisely the two clauses of `fanizza-native-signal-groupification`.


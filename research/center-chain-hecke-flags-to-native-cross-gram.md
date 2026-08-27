---
rg: 2
id: center-chain-hecke-flags-to-native-cross-gram
kind: route
title: Use the nested center-chain Hecke flags as the native two-scale transports
target: binary-leavitt-native-two-scale-cross-gram-positive
requires:
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
  - center-chain-hecke-flags-authenticate-native-occurrences
---

By the occurrence-typing input, the two actual stabilized selector
transports restrict to the polar maps computed in
`center-chain-hecke-polar-supports-are-nested-pauli-flags`.  Equation
`(CHS8)` then gives `(NCG1)` with `gamma=1/8` relative to the character
source corner, and `(CHS9)` gives the two mixed source-Pauli commutators
with zero error.  The support traces in `(CHS6)` are exactly the controlled
quarter and eighth label fractions, so this is the prescribed native pair
rather than an unrelated rectangular completion.  Fixed-word telescoping
and finite-packet exactification turn the exact calculation into the
required `o(1)` normalized-Hilbert--Schmidt statement for canonical
microstates.


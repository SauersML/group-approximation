---
rg: 2
id: center-chain-common-source-saturation-proof
kind: route
title: Restrict the four positive character projections to the common positive character
target: center-chain-common-source-saturates-four-hecke-flags
requires:
  - center-chain-four-hecke-flags-have-native-ranks
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

The generators defining `r_1,r_2,p_1,p_2` in `(FHF2)` are among the seven
root directions adjoined to `H` in `L_0`.  Formula `(MCS4)` assigns the
positive character value to every one of them.  Therefore each associated
positive character projection fixes `Q=e_(L_0,lambda_0)`, which proves
`(CSF1)`.  Multiplication on either side by `E<=Q` gives the last assertion.


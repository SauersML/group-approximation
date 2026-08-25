---
rg: 2
id: native-prefix-whiteheads-restrict-to-center-chain-hecke-flags
kind: route
title: Restrict the two native prefix Whiteheads to the nested center-chain Hecke supports
target: center-chain-hecke-flags-authenticate-native-occurrences
requires:
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
  - odd-leavitt-prefix-whitehead-transport
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

**INVALIDATED PROPOSAL.**  Use the literal partial-Whitehead words for the
two coefficients `s_(00)t_0` and `s_(000)t_(00)`, compress both to the
smaller Hecke support `p_2`, and identify their polar maps with those of
`eA_1e` and `eA_2A_1e`.  If `p_2` is not reducing, pass to the largest fixed
positive subcorner of `p_2` reducing both words.

`native-whitehead-corner-collapses-hecke-flags`
computes this proposal exactly.  Neither word reduces `p_2`; their two
compressed supports have the same relative trace `1/16`, not the Hecke
traces `1/4,1/8`.  The largest common reducing subcorner is positive, but
there `A_2` acts as `+1`, so the two Hecke polar maps coincide.  Meanwhile
the Whiteheads retain two distinct adjacent-swap actions.  Thus restriction
cannot supply the required identification.  A viable occurrence compiler
must use an additional mixed word row rather than only compress the two
native Whiteheads.

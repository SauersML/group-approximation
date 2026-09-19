---
rg: 2
id: primitive-menu-odd-native-hecke-coercivity
kind: route
title: Derive native Hecke coercivity from an odd mixed primitive relator in the fixed menu
target: center-chain-common-source-authenticates-native-covariances
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - odd-leavitt-prefix-whitehead-transport
---

**INVALIDATED PRIMITIVE-RELATOR PROPOSAL.**  Search the primitive
binary-Leavitt/Steinberg occurrence relators for one in which an actual
native Whitehead row occurs with odd parity together with an unequal-scale
center-chain Hecke word, and use that single relator directly to prove the
spectral-mass estimate `(MFK6)`.

`primitive-native-hecke-relators-have-no-odd-mixed-occurrence` invalidates
this route.  The primitive mixed Hecke triangles authenticate only the
first/third Whitehead factors `X_i`, which occur twice in the native word.
The sole odd factors `Y_i` occur in no unequal-scale primitive triangle.
There is a genuine **derived** order-seven occurrence relation, now recorded
by `native-whitehead-hecke-head-has-order-seven-anchor`; it lies outside the
scope of this primitive-relator audit and is treated separately.

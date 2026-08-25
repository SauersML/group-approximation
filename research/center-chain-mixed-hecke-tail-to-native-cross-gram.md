---
rg: 2
id: center-chain-mixed-hecke-tail-to-native-cross-gram
kind: route
title: Use the four Hecke flags and their mixed polar tails to obtain the native two-scale cross-Gram
requires:
  - center-chain-four-hecke-flags-have-native-ranks
  - center-chain-mixed-hecke-polars-share-a1-tail
  - center-chain-mixed-hecke-tail-quantitative-typing
target: binary-leavitt-native-two-scale-cross-gram-positive
---

The two individual B-side flags supply the native source ranks `1/2,1/4`,
the cumulative A-side flags supply the target ranks `1/4,1/8`, and the two
mixed source-to-target cross-Grams have polar words whose squares are exactly
the prescribed literal coefficient roots.  Once
`center-chain-mixed-hecke-tail-quantitative-typing` synchronizes their common
right tail on model-dependent spectral cuts and charges the discarded mass
to approximate relation defects, its fourth conclusion is precisely the
positive native two-scale cross-Gram and mixed-Pauli statement targeted here.

This route makes no fixed exact occurrence assertion and therefore does not
cross the canonical regular-trace firewall.

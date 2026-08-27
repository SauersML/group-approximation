---
rg: 2
id: p3-denominator-steinberg-blindness-proof
kind: route
title: Cancel the multiplicity normalizer before applying the Chevalley commutator
target: p3-denominator-steinberg-word-is-multiplicity-blind
requires:
  - denominator-transport-only-conjugates-p3-multiplicity-reservoirs
  - finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge
---

Insert `rho(h)=W_h tensor V` and `rho(x)=pi(x) tensor I` into `(DSB1)`.
The adjacent `V,V^*` cancel inside the conjugated root, leaving the ordinary
Chevalley relation on the oscillator factor tensored with the identity.
Choosing the two-dimensional swap and a half projection gives `(DSB4)`.
For the full finite transition table, use the inverse twisted-regular
groupoid gauge; cocycle cancellation makes the normalizer table honest, and
the denominator-conjugated root triangles add no further multiplicity
equation.

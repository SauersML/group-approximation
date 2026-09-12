---
rg: 2
id: order-seven-active-cut-gives-el20-native-cross-gram
kind: route
title: Remove both reservoir involutions by the inherited order-seven anchors
target: binary-leavitt-el20-arbitrary-profile-native-cross-gram
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - order-seven-anchor-stops-at-whitehead-compression-leakage
  - finite-coordinate-el20-active-cut-inherits-order-seven-anchor
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
---

Apply the finite-coordinate claim on the positive-density EL20 active core.
On its common source, the only remaining discrepancy between each actual
native occurrence and its Hecke head is the commuting multiplicity
involution `D_i`.  The compressed order-seven word is the ungauged
order-seven word times `D_i^7=D_i`.  The exact coercivity identity `(OWH6)`
and telescoping of the vanishing compression errors therefore give

```text
||D_i-Q||_2=o(1),                  i=1,2.              (1)
```

Thus both actual transports are `o_2(1)` from the two common-source Hecke
maps on the same positive-density cut.  Their exact Hecke cross-Gram is a
unitary on the common source, so `(1)` gives `(EAP1)` (indeed with relative
Gram tending to one on the retained cut).  The mixed Pauli commutators are
preserved by `(OCI4)` and the exact common-source factorization.  This proves
the direct-elementary arbitrary-profile cross-Gram claim without a
Steinberg lift or canonical trace profile.

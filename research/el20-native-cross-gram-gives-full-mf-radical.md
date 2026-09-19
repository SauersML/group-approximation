---
rg: 2
id: el20-native-cross-gram-gives-full-mf-radical
kind: route
title: Contradict the two affine gauge ranks directly in the simple elementary group
target: property-t-free-el20-full-mf-radical
requires:
  - binary-leavitt-el20-arbitrary-profile-native-cross-gram
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - binary-leavitt-elementary-group-is-simple
---

Suppose a homomorphism from `EL_20(R)` to a norm matrix corona keeps
`z=e_13(s_1t_1)` nontrivial.  Its finite-order spectral core has positive
normalized rank.  The direct EL20 arbitrary-profile cross-Gram theorem and
the polar-corner lemma align the two actual scale transports on one positive
corner.  The mixed-Pauli theorem puts their relative polar in the common
multiplicity commutant.  The two selector rows then force the same gauge
fraction toward both `1/2` and `5/6`, contradicting the established affine
rank gap.  Hence every corona homomorphism kills `z`.

The MF radical is normal.  The marked elementary root is nonidentity, and
`EL_20(R)` is simple by the internal root-detection theorem (equivalently,
the explicit nonzero-root normal-generation theorem applies).  Therefore a
radical containing `z` is the whole group, proving `(EMF1)`.  This direction
uses no Steinberg kernel and no quotient-permanence assertion.

